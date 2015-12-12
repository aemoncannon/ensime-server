package org.ensime.core.javac

import akka.event.slf4j.SLF4JLogging
import com.sun.source.tree.Scope
import com.sun.source.tree.Tree
import com.sun.source.tree.{ IdentifierTree, MemberSelectTree }
import com.sun.source.util.{ JavacTask, TreePath, Trees }
import java.io.{ File, FileInputStream, InputStream }
import java.net.URI
import java.nio.charset.Charset
import java.util.Locale
import java.util.concurrent.ConcurrentHashMap
import javax.lang.model.`type`.TypeKind
import javax.lang.model.`type`.TypeMirror
import javax.tools._
import org.ensime.api._
import org.ensime.core.DocSigPair
import org.ensime.model.LineSourcePositionHelper
import org.ensime.indexer.{ EnsimeVFS, SearchService }
import org.ensime.util.ReportHandler
import org.ensime.util.file._
import scala.collection.JavaConverters._
import scala.reflect.internal.util.{ BatchSourceFile, RangePosition, SourceFile }
import scala.tools.nsc.Settings
import scala.tools.nsc.interactive.CompilerControl
import scala.tools.nsc.io.AbstractFile
import scala.tools.nsc.reporters.Reporter
import scala.tools.refactoring.analysis.GlobalIndexes
import javax.lang.model.element.ElementKind
import javax.lang.model.element.ExecutableElement
import javax.lang.model.element.TypeElement

class JavaCompiler(
    val config: EnsimeConfig,
    val reportHandler: ReportHandler,
    val search: SearchService,
    val vfs: EnsimeVFS
) extends JavaDocFinding with JavaCompletion with JavaSourceFinding with Helpers with SLF4JLogging {

  private val listener = new JavaDiagnosticListener()
  private val silencer = new SilencedDiagnosticListener()
  private val cp = (config.allJars ++ config.targetClasspath).mkString(File.pathSeparator)
  private var workingSet = new ConcurrentHashMap[String, JavaFileObject]()

  // needs to be recreated in JDK6. JDK7 seems more capable of reuse.
  def getTask(
    lint: String,
    listener: DiagnosticListener[JavaFileObject],
    files: java.lang.Iterable[JavaFileObject]
  ): JavacTask = {
    // TODO: take a charset for each invocation
    val compiler = ToolProvider.getSystemJavaCompiler()
    val fileManager = compiler.getStandardFileManager(listener, null, DefaultCharset)
    compiler.getTask(null, fileManager, listener, List(
      "-cp", cp, "-Xlint:" + lint, "-proc:none"
    ).asJava, null, files).asInstanceOf[JavacTask]
  }

  def internSource(sf: SourceFileInfo): JavaFileObject = {
    val jfo = getJavaFileObject(sf)
    workingSet.put(sf.file.getAbsolutePath, jfo)
    jfo
  }

  def askTypecheckFiles(files: List[SourceFileInfo]): Unit = {
    reportHandler.clearAllJavaNotes()
    for (sf <- files) {
      internSource(sf)
    }
    typecheckAll()
  }

  def askLinkPos(fqn: String, file: SourceFileInfo): Option[SourcePosition] = {
    val infos = typecheckForUnits(List(file))
    infos.headOption.flatMap { info => findInCompiledUnit(info, fqn) }
  }

  def askTypeAtPoint(file: SourceFileInfo, offset: Int): Option[TypeInfo] = {
    pathToPoint(file, offset) flatMap {
      case (info: CompilationInfo, path: TreePath) =>
        getTypeMirror(info, offset).map(typeMirrorToTypeInfo)
    }
  }

  def askSymbolAtPoint(file: SourceFileInfo, offset: Int): Option[SymbolInfo] = {
    pathToPoint(file, offset) flatMap {
      case (info: CompilationInfo, path: TreePath) =>
        def withName(name: String): Option[SymbolInfo] = {
          val tpeMirror = Option(info.getTrees().getTypeMirror(path))
          val nullTpe = new BasicTypeInfo("NA", -1, DeclaredAs.Nil, "NA", List.empty, List.empty, None, None)
          Some(SymbolInfo(
            name,
            name,
            findDeclPos(info, path),
            tpeMirror.map(typeMirrorToTypeInfo).getOrElse(nullTpe),
            tpeMirror.map(_.getKind == TypeKind.EXECUTABLE).getOrElse(false),
            None
          ))
        }
        path.getLeaf match {
          case t: IdentifierTree => withName(t.getName.toString)
          case t: MemberSelectTree => withName(t.getIdentifier.toString)
          case _ => None
        }
    }
  }

  def askDocSignatureAtPoint(file: SourceFileInfo, offset: Int): Option[DocSigPair] = {
    pathToPoint(file, offset) flatMap {
      case (info: CompilationInfo, path: TreePath) =>
        docSignature(info, path)
    }
  }

  def askCompletionsAtPoint(
    file: SourceFileInfo, offset: Int, maxResults: Int, caseSens: Boolean
  ): CompletionInfoList = {
    completionsAt(file, offset, maxResults, caseSens)
  }

  protected def pathToPoint(file: SourceFileInfo, offset: Int): Option[(CompilationInfo, TreePath)] = {
    val infos = typecheckForUnits(List(file))
    infos.headOption.flatMap { info =>
      val path = Option(new TreeUtilities(info).pathFor(offset))
      path.map { p => (info, p) }
    }
  }

  protected def scopeForPoint(file: SourceFileInfo, offset: Int): Option[(CompilationInfo, Scope)] = {
    val infos = typecheckForUnits(List(file))
    infos.headOption.flatMap { info =>
      val path = Option(new TreeUtilities(info).scopeFor(offset))
      path.map { p => (info, p) }
    }
  }

  private def typeMirrorToTypeInfo(tm: TypeMirror): TypeInfo = {
    BasicTypeInfo(tm.toString, -1, DeclaredAs.Class, tm.toString, List(), List(), Some(EmptySourcePosition()), None)
  }

  private def getTypeMirror(info: CompilationInfo, offset: Int): Option[TypeMirror] = {
    val path = Option(new TreeUtilities(info).pathFor(offset))
    // Uncomment to debug the AST path.
    //for (p <- path) { for (t <- p) { System.err.println(t.toString()) } }
    path.flatMap { p => Option(info.getTrees().getTypeMirror(p)) }
  }

  private def typecheckAll(): Unit = {
    val task = getTask("all", listener, workingSet.values)
    val t = System.currentTimeMillis()
    task.parse()
    task.analyze()
    log.info("Parsed and analyzed: " + (System.currentTimeMillis() - t) + "ms")
  }

  private def typecheckForUnits(inputs: List[SourceFileInfo]): Vector[CompilationInfo] = {
    // We only want the compilation units for inputs, but we need to typecheck them w.r.t
    // the full working set.
    val inputJfos = inputs.map { sf => internSource(sf).toUri }.toSet
    val task = getTask("none", silencer, workingSet.values)
    val t = System.currentTimeMillis()
    val units = task.parse().asScala.filter { unit => inputJfos.contains(unit.getSourceFile.toUri) }
      .map(new CompilationInfo(task, _)).toVector
    task.analyze()
    log.info("Parsed and analyzed for trees: " + (System.currentTimeMillis() - t) + "ms")
    units
  }

  private class JavaObjectWithContents(val f: File, val contents: String)
      extends SimpleJavaFileObject(f.toURI, JavaFileObject.Kind.SOURCE) {
    override def getCharContent(ignoreEncodingErrors: Boolean): CharSequence = contents
  }

  private class JavaObjectFromFile(val f: File)
      extends SimpleJavaFileObject(f.toURI, JavaFileObject.Kind.SOURCE) {
    override def getCharContent(ignoreEncodingErrors: Boolean): CharSequence = f.readString
    override def openInputStream(): InputStream = new FileInputStream(f)
  }

  private def getJavaFileObject(sf: SourceFileInfo): JavaFileObject = sf match {
    case SourceFileInfo(f, None, None) => new JavaObjectFromFile(f)
    case SourceFileInfo(f, Some(contents), None) => new JavaObjectWithContents(f, contents)
    case SourceFileInfo(f, None, Some(contentsIn)) => new JavaObjectWithContents(f, contentsIn.readString)
  }

  private class JavaDiagnosticListener extends DiagnosticListener[JavaFileObject] with ReportHandler {
    def report(diag: Diagnostic[_ <: JavaFileObject]): Unit = {
      reportHandler.reportJavaNotes(List(
        Note(
          diag.getSource().getName(),
          diag.getMessage(Locale.ENGLISH),
          diag.getKind() match {
            case Diagnostic.Kind.ERROR => NoteError
            case Diagnostic.Kind.WARNING => NoteWarn
            case Diagnostic.Kind.MANDATORY_WARNING => NoteWarn
            case _ => NoteInfo
          },
          diag.getStartPosition() match {
            case x if x > -1 => x.toInt
            case _ => diag.getPosition().toInt
          },
          diag.getEndPosition().toInt,
          diag.getLineNumber().toInt,
          diag.getColumnNumber().toInt
        )
      ))
    }
  }

  private class SilencedDiagnosticListener extends DiagnosticListener[JavaFileObject] with ReportHandler {
    def report(diag: Diagnostic[_ <: JavaFileObject]): Unit = {}
  }

}

