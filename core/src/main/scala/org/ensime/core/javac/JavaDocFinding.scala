package org.ensime.core.javac

import com.sun.source.tree.{ MemberSelectTree, MethodInvocationTree, Tree }
import com.sun.source.util.TreePath
import javax.lang.model.`type`.{ DeclaredType, PrimitiveType, ReferenceType, TypeKind, TypeMirror }
import javax.lang.model.element.{ Element, ExecutableElement, TypeElement }
import javax.lang.model.util.{ ElementFilter, Elements }
import org.ensime.core.{ DocFqn, DocSig, DocSigPair }
import scala.collection.JavaConversions._

trait JavaDocFinding {

  def docSignature(info: CompilationInfo, p: TreePath): Option[DocSigPair] = {
    val leaf = p.getLeaf
    val enclosing = Option(p.getParentPath.getLeaf)
    (leaf, enclosing) match {
      case (t: MemberSelectTree, Some(m: MethodInvocationTree)) => {
        val name = t.getIdentifier().toString()
        fqn(info, t.getExpression()).map { fqn =>
          val sig = DocSig(fqn, memberSig(info, m, candidates(info, t.getExpression, name), name))
          DocSigPair(sig, sig)
        }
      }
      case (t: Tree, _) => {
        fqn(info, p).map { fqn =>
          val sig = DocSig(fqn, None)
          DocSigPair(sig, sig)
        }
      }
    }
  }

  private def candidates(info: CompilationInfo, target: Tree, name: String): List[ExecutableElement] = {
    typeElement(info, target).map { el =>
      el match {
        case tel: TypeElement => {
          val elements: Elements = info.getElements()
          ElementFilter.methodsIn(
            elements.getAllMembers(tel).filter { e => e.getSimpleName.toString() == name }
          ).toList
        }
        case _ => {
          List()
        }
      }
    }.getOrElse(List())
  }

  private def memberSig(info: CompilationInfo, m: MethodInvocationTree,
    candidates: List[ExecutableElement], name: String): Option[String] = {
    val args = m.getArguments
    val byArity = candidates.filter { c => c.getParameters.length == args.length }
    val withTypeDeltas = byArity.map { c => typeDeltas(info, m, c) }.toArray
    val compatible = withTypeDeltas.filter { case (c, deltas) => !deltas.contains(Int.MaxValue) }
    val sorted = compatible.sortWith { (c1, c2) => c1._2.sum < c2._2.sum }
    sorted.headOption.map {
      case (c, deltas) =>
        val args = c.getParameters.map { p => fqn(info, p.asType).map(_.mkString).getOrElse("NA") }.mkString(",")
        s"$name($args)"
    }
  }

  private def typeMirror(info: CompilationInfo, t: Tree): Option[TypeMirror] = {
    Option(info.getTrees().getTypeMirror(info.getTrees().getPath(info.getCompilationUnit(), t)))
  }

  private def typeElement(info: CompilationInfo, t: Tree): Option[Element] = {
    typeMirror(info, t).map(info.getTypes().asElement)
  }

  private def fqn(info: CompilationInfo, p: TreePath): Option[DocFqn] = {
    val tm = Option(info.getTrees().getTypeMirror(p))
    tm.flatMap { tm => fqn(info, tm) }
  }

  private def fqn(info: CompilationInfo, t: Tree): Option[DocFqn] = {
    Option(info.getTrees().getPath(info.getCompilationUnit(), t)).flatMap { p => fqn(info, p) }
  }

  private def fqn(info: CompilationInfo, tm: TypeMirror): Option[DocFqn] = {

    def parseFqn(qualifiedName: String) = {
      val (front, back) = qualifiedName.split("\\.").partition { s => s.forall(Character.isLowerCase) }
      DocFqn(front.mkString("."), back.mkString("."))
    }

    // "Using instanceof is not necessarily a reliable idiom for
    // determining the effective class of an object in this modeling
    // hierarchy since an implementation may choose to have a single
    // object implement multiple TypeMirror subinterfaces." --
    // TypeMirror docs
    tm match {
      case tm: DeclaredType if tm.getKind == TypeKind.DECLARED => {
        tm.asElement match {
          case te: TypeElement => Some(parseFqn(te.getQualifiedName.toString))
          case _ => {
            None
          }
        }
      }
      case tm: PrimitiveType if tm.getKind.isPrimitive => Some(DocFqn("", tm.toString))
      case _ => None
    }
  }

  // For each (argument, parameter) pair compute an integer distance between them.
  // Int.MaxValue denotes an incompatible pairing (e.g. reference argument supplied for
  // primitive param). 0 denotes type equality. 
  private def typeDeltas(info: CompilationInfo, m: MethodInvocationTree, c: ExecutableElement): (ExecutableElement, Array[Int]) = {
    val types = info.getTypes()
    val args = m.getArguments
    val params = c.getParameters
    val result = new Array[Int](args.length)
    for (i <- 0 to (args.length - 1)) {
      val param = Option(params.get(i).asType);
      val arg = typeMirror(info, args.get(i))
      result(i) = (param, arg) match {
        case (Some(p: TypeMirror), Some(a: TypeMirror)) if types.isSameType(p, a) => 0
        case (Some(p: PrimitiveType), Some(a: PrimitiveType)) if types.isAssignable(a, p) => 1
        case (Some(p: ReferenceType), Some(a: ReferenceType)) if types.isSubtype(a, p) => 1
        case _ => Int.MaxValue
      }
    }
    (c, result)
  }

}
