package org.ensime.core.javac

import com.sun.source.tree.{ MemberSelectTree, MethodInvocationTree, Tree, IdentifierTree }
import com.sun.source.util.TreePath
import javax.lang.model.`type`.{ DeclaredType, PrimitiveType, ReferenceType, TypeKind, TypeMirror }
import javax.lang.model.element.{ Element, ExecutableElement, PackageElement, TypeElement, VariableElement }
import javax.lang.model.util.{ ElementFilter, Elements }
import org.ensime.core.{ DocFqn, DocSig, DocSigPair, CompletionUtil }
import org.ensime.util.FileUtils
import org.ensime.api._
import scala.collection.JavaConversions._
import java.nio.charset.Charset
import com.sun.source.tree.Scope
import scala.collection.mutable.HashSet;
import scala.collection.mutable.ArrayBuffer;

trait JavaCompletion { self: JavaCompiler =>

  import CompletionUtil._

  def completionsAt(info: SourceFileInfo, offset: Int, maxResultsArg: Int, caseSens: Boolean): CompletionInfoList = {
    val s = contentsAsString(info, charset)

    val preceding = s.slice(Math.max(0, offset - 100), offset)

    System.err.println("PRECEDING: " + preceding)

    val defaultPrefix = JavaIdentRegexp.findFirstMatchIn(preceding) match {
      case Some(m) => m.group(1)
      case _ => ""
    }

    System.err.println("PREFIX: " + defaultPrefix)

    val constructing = ConstructingRegexp.findFirstMatchIn(preceding).isDefined

    System.err.println("CONSTRUCTING: " + constructing)

    val indexAfterTarget = offset - defaultPrefix.length - 1

    val precedingChar = s(indexAfterTarget)

    val isMemberAccess = precedingChar == '.'

    (if (ImportSubtypeRegexp.findFirstMatchIn(preceding).isDefined) {
      // Erase the trailing partial subtype (it breaks type resolution).
      val patched = s.substring(0, indexAfterTarget) + " " + s.substring(indexAfterTarget + defaultPrefix.length + 1);
      (pathToPoint(SourceFileInfo(info.file, Some(patched), None), indexAfterTarget - 1) map {
        case (info: CompilationInfo, path: TreePath) => {
          memberCandidates(info, path.getLeaf, defaultPrefix, true, caseSens)
        }
      })
    } else if (ImportRegexp.findFirstMatchIn(preceding).isDefined) {
      (pathToPoint(info, indexAfterTarget) flatMap {
        case (info: CompilationInfo, path: TreePath) => {
          getEnclosingMemberSelectTree(path).map { m =>
            packageMemberCandidates(info, m, defaultPrefix, caseSens)
          }
        }
      })
    } else if (isMemberAccess) {
      // TODO how to avoid allocating a new string? buffer of immutable string slices?
      // Erase the trailing partial member (it breaks type resolution).
      val patched = s.substring(0, indexAfterTarget) + ".wait()" + s.substring(indexAfterTarget + defaultPrefix.length + 1);
      (pathToPoint(SourceFileInfo(info.file, Some(patched), None), indexAfterTarget) flatMap {
        case (info: CompilationInfo, path: TreePath) => {
          getEnclosingMemberSelectTree(path).map { m =>
            memberCandidates(info, m.getExpression(), defaultPrefix, false, caseSens)
          }
        }
      })
    } else {
      (scopeForPoint(info, indexAfterTarget) map {
        case (info: CompilationInfo, s: Scope) => {
          scopeMemberCandidates(info, s, defaultPrefix, caseSens)
        }
      })
    }).getOrElse(CompletionInfoList(defaultPrefix, List()))
  }

  private def getEnclosingMemberSelectTree(path: TreePath): Option[MemberSelectTree] = {
    var p = path
    while (p != null) {
      p.getLeaf match {
        case m: MemberSelectTree => return Some(m)
        case _ => {}
      }
      p = p.getParentPath
    }
    None
  }

  private def selectedPackageName(m: MemberSelectTree): String = {
    val name = m.getIdentifier.toString
    m.getExpression match {
      case m: MemberSelectTree => selectedPackageName(m) + "." + name
      case i: IdentifierTree => i.getName.toString() + "." + name
      case _ => name
    }
  }

  private def packageMemberCandidates(
    info: CompilationInfo,
    select: MemberSelectTree,
    prefix: String,
    caseSense: Boolean
  ): CompletionInfoList = {
    val pkg = selectedPackageName(select)
    val candidates = (Option(info.getElements.getPackageElement(pkg)) map { p: PackageElement =>
      p.getEnclosedElements().flatMap { e => filterElement(e, prefix, caseSense, true) }
    }).getOrElse(List())
    CompletionInfoList(prefix, candidates.toList)
  }

  private def filterElement(e: Element, prefix: String, caseSense: Boolean, typesOnly: Boolean): Option[CompletionInfo] = {
    val s = e.getSimpleName.toString
    if (matchesPrefix(s, prefix, matchEntire = false, caseSens = caseSense) && !s.contains("$")) {
      e match {
        case e: ExecutableElement if !typesOnly => Some(methodInfo(e))
        case e: VariableElement if !typesOnly => Some(fieldInfo(e))
        case e: TypeElement => Some(typeInfo(e))
        case _ => None
      }
    } else None
  }

  private def scopeMemberCandidates(
    info: CompilationInfo,
    scope: Scope,
    prefix: String,
    caseSense: Boolean
  ): CompletionInfoList = {
    var candidates = ArrayBuffer[CompletionInfo]()

    // Note Scope#getLocalElements does not include fields / members of
    // enclosing classes. Need to add those manually.
    //
    def addTypeMembers(tel: TypeElement): Unit = {
      for (el <- info.getElements().getAllMembers(tel)) {
        for (info <- filterElement(el, prefix, caseSense, false)) {
          candidates += info
        }
      }
    }
    for (tel <- Option(scope.getEnclosingClass())) {
      addTypeMembers(tel)
      var t = tel.getEnclosingElement()
      while (t != null) {
        t match {
          case tel: TypeElement => addTypeMembers(tel)
          case _ =>
        }
        t = t.getEnclosingElement()
      }
    }

    var s = scope
    while (s != null) {
      for (el <- s.getLocalElements()) {
        for (info <- filterElement(el, prefix, caseSense, false)) {
          candidates += info
        }
      }
      s = s.getEnclosingScope()
    }
    CompletionInfoList(prefix, candidates.toList)
  }

  private def memberCandidates(
    info: CompilationInfo,
    target: Tree,
    prefix: String,
    importing: Boolean,
    caseSense: Boolean
  ): CompletionInfoList = {
    val candidates = typeElement(info, target).map { el =>
      el match {
        case tel: TypeElement => {
          val elements: Elements = info.getElements()
          elements.getAllMembers(tel).flatMap { e =>
            filterElement(e, prefix, caseSense, importing)
          }
        }
        case e => {
          System.err.println("Unrecognized type element " + e)
          List()
        }
      }
    }.getOrElse(List())
    CompletionInfoList(prefix, candidates.toList)
  }

  private def methodInfo(e: ExecutableElement) = {
    val s = e.getSimpleName.toString
    CompletionInfo(
      s,
      CompletionSignature(
        List(e.getParameters().map { p => (p.getSimpleName.toString, localTypeName(p.asType)) }.toList),
        localTypeName(e.getReturnType())
      ),
      -1, true, 0, None
    )
  }

  private def fieldInfo(e: VariableElement) = {
    val s = e.getSimpleName.toString
    CompletionInfo(
      s, CompletionSignature(List(), localTypeName(e.asType())), -1, false, 0, None
    )
  }

  private def typeInfo(e: TypeElement) = {
    val s = e.getSimpleName.toString
    CompletionInfo(
      s, CompletionSignature(List(), localTypeName(e.asType())), -1, false, 0, None
    )
  }

  private def localTypeName(tm: TypeMirror) = {
    val s = tm.toString
    val (front, back) = s.split("\\.").partition { s => s.forall(Character.isLowerCase) }
    if (back.isEmpty) s else back.mkString(".")
  }

  private def typeMirror(info: CompilationInfo, t: Tree): Option[TypeMirror] = {
    Option(info.getTrees().getTypeMirror(info.getTrees().getPath(info.getCompilationUnit(), t)))
  }

  private def typeElement(info: CompilationInfo, t: Tree): Option[Element] = {
    typeMirror(info, t).map(info.getTypes().asElement)
  }

  private def contentsAsString(sf: SourceFileInfo, charset: Charset) = sf match {
    case SourceFileInfo(f, None, None) => FileUtils.readFile(f, charset).fold(e => throw e, s => s)
    case SourceFileInfo(f, Some(contents), None) => contents
    case SourceFileInfo(f, None, Some(contentsIn)) => FileUtils.readFile(contentsIn, charset).fold(e => throw e, s => s)
  }

}
