package org.ensime.core

import java.io.{ File => JFile }
import java.nio.charset.Charset
import java.nio.charset.StandardCharsets

import akka.actor._
import akka.event.LoggingReceive.withLabel
import akka.pattern.pipe
import org.ensime.api._
import org.ensime.core.javac.JavaCompiler
import org.ensime.indexer.{ EnsimeVFS, SearchService }
import org.ensime.model._
import org.ensime.util.{ PresentationReporter, ReportHandler, FileUtils }
import org.slf4j.LoggerFactory
import org.ensime.util.file._

import scala.reflect.internal.util.{ OffsetPosition, RangePosition, SourceFile }
import scala.tools.nsc.Settings
import scala.tools.nsc.interactive.Global
import scala.util.Try

case class CompilerFatalError(e: Throwable)

/**
 * Information necessary to create a javadoc or scaladoc URI for a
 * particular type or type member.
 */
case class DocFqn(pack: String, typeName: String) {
  def mkString: String = if (pack.isEmpty) typeName else pack + "." + typeName
  def inPackage(prefix: String): Boolean = pack == prefix || pack.startsWith(prefix + ".")
  def javaStdLib: Boolean = inPackage("java") || inPackage("javax")
  def scalaStdLib: Boolean = inPackage("scala")
}
case class DocSig(fqn: DocFqn, member: Option[String])

/**
 * We generate DocSigs for java and scala at the same time, since we
 * don't know a priori whether the docs will be in scaladoc or javadoc
 * format.
 */
case class DocSigPair(scala: DocSig, java: DocSig)

class Analyzer(
    broadcaster: ActorRef,
    indexer: ActorRef,
    search: SearchService,
    implicit val config: EnsimeConfig,
    implicit val vfs: EnsimeVFS
) extends Actor with Stash with ActorLogging with RefactoringHandler {

  private var allFilesMode = false

  private var settings: Settings = _
  private var reporter: PresentationReporter = _

  protected var scalaCompiler: Option[RichCompilerControl] = _

  protected var javaCompiler: JavaCompiler = _

  override def preStart(): Unit = {
    val presCompLog = LoggerFactory.getLogger(classOf[Global])

    settings = new Settings(presCompLog.error)
    settings.YpresentationDebug.value = presCompLog.isTraceEnabled
    settings.YpresentationVerbose.value = presCompLog.isDebugEnabled
    settings.verbose.value = presCompLog.isDebugEnabled
    settings.usejavacp.value = false
    config.allJars.find(_.getName.contains("scala-library")) match {
      case Some(scalaLib) => settings.bootclasspath.value = scalaLib.getAbsolutePath
      case None => log.warning("scala-library.jar was not present")
    }
    settings.classpath.value = config.compileClasspath.mkString(JFile.pathSeparator)
    settings.processArguments(config.compilerArgs, processAll = false)
    presCompLog.debug("Presentation Compiler settings:\n" + settings)

    reporter = new PresentationReporter(new ReportHandler {
      override def messageUser(str: String): Unit = {
        broadcaster ! SendBackgroundMessageEvent(str, 101)
      }
      override def clearAllScalaNotes(): Unit = {
        broadcaster ! ClearAllScalaNotesEvent
      }
      override def reportScalaNotes(notes: List[Note]): Unit = {
        broadcaster ! NewScalaNotesEvent(isFull = false, notes)
      }
    })
    reporter.disable() // until we start up

    scalaCompiler = makeScalaCompiler()
    javaCompiler = new JavaCompiler(
      config,
      Charset.forName(settings.encoding.value),
      indexer,
      new ReportHandler {
        override def messageUser(str: String): Unit = {
          broadcaster ! SendBackgroundMessageEvent(str, 101)
        }
        override def clearAllJavaNotes(): Unit = {
          broadcaster ! ClearAllJavaNotesEvent
        }
        override def reportJavaNotes(notes: List[Note]): Unit = {
          broadcaster ! NewJavaNotesEvent(isFull = false, notes)
        }
      }
    )

    broadcaster ! SendBackgroundMessageEvent("Initializing Analyzer. Please wait...")

    scalaCompiler match {
      case Some(cc) => {
        cc.askNotifyWhenReady()
        if (config.sourceMode) cc.askReloadAllFiles()
      }
      case _ => self ! FullTypeCheckCompleteEvent
    }
  }

  protected def makeScalaCompiler() = {
    try {
      Some(new RichPresentationCompiler(
        config, settings, reporter, self, indexer, search
      ))
    } catch {
      case e: Exception => {
        log.warning("Failed to start the scala compiler", e)
        None
      }
    }
  }

  protected def restartCompiler(keepLoaded: Boolean): Unit = {
    log.warning("Restarting the Presentation Compiler")
    val files = scalaCompiler.map(_.loadedFiles)
    for (cc <- scalaCompiler) {
      cc.askShutdown()
    }
    scalaCompiler = makeScalaCompiler()
    for (cc <- scalaCompiler) {
      if (keepLoaded) {
        for (fs <- files) {
          cc.askReloadFiles(fs)
        }
      }
      cc.askNotifyWhenReady()
    }
    broadcaster ! CompilerRestartedEvent
  }

  override def postStop(): Unit = {
    for (cc <- scalaCompiler) {
      Try(cc.askClearTypeCache())
      Try(cc.askShutdown())
    }
  }

  def charset: Charset = scalaCompiler.map(_.charset).getOrElse(StandardCharsets.UTF_8)

  def receive: Receive = startup

  def startup: Receive = withLabel("startup") {
    case FullTypeCheckCompleteEvent =>
      reporter.enable()
      // legacy clients expect to see AnalyzerReady and a
      // FullTypeCheckCompleteEvent on connection.
      broadcaster ! Broadcaster.Persist(AnalyzerReadyEvent)
      broadcaster ! Broadcaster.Persist(FullTypeCheckCompleteEvent)
      context.become(ready)
      unstashAll()

    case other =>
      stash()
  }

  def ready: Receive = withLabel("ready") {
    case ReloadExistingFilesEvent if allFilesMode =>
      log.info("Skipping reload, in all-files mode")
    case ReloadExistingFilesEvent =>
      restartCompiler(keepLoaded = true)

    case FullTypeCheckCompleteEvent =>
      broadcaster ! FullTypeCheckCompleteEvent

    case req: RpcAnalyserRequest =>
      // fommil: I'm not entirely sure about the logic of
      // enabling/disabling the reporter so I am reluctant to refactor
      // this, but it would perhaps be simpler if we enable the
      // reporter when the presentation compiler is loaded, and only
      // disable it when we explicitly want it to be quiet, instead of
      // enabling on every incoming message.
      reporter.enable()
      allTheThings(req)
  }

  import context.dispatcher

  def allTheThings: PartialFunction[RpcAnalyserRequest, Unit] = {
    case RemoveFileReq(file: File) =>
      for (cc <- scalaCompiler) {
        cc.askRemoveDeleted(file)
      }
      sender ! VoidResponse
    case TypecheckAllReq =>
      allFilesMode = true
      for (cc <- scalaCompiler) {
        cc.askRemoveAllDeleted()
        cc.askReloadAllFiles()
        cc.askNotifyWhenReady()
      }
      sender ! VoidResponse
    case UnloadAllReq =>
      if (config.sourceMode) {
        log.info("in source mode, will reload all files")
        for (cc <- scalaCompiler) cc.askRemoveAllDeleted()
        restartCompiler(keepLoaded = true)
      } else {
        allFilesMode = false
        restartCompiler(keepLoaded = false)
      }
      sender ! VoidResponse
    case TypecheckFileReq(fileInfo) =>
      sender ! handleReloadFiles(List(fileInfo))
    case TypecheckFilesReq(files) =>
      sender ! handleReloadFiles(files.map(SourceFileInfo(_)))
    case req: PrepareRefactorReq =>

      sender ! scalaCompiler.map(handleRefactorPrepareRequest(_, req)).getOrElse(VoidResponse)
    case req: ExecRefactorReq =>
      sender ! scalaCompiler.map(handleRefactorExec(_, req)).getOrElse(VoidResponse)
    case req: CancelRefactorReq =>
      sender ! handleRefactorCancel(req)
    case CompletionsReq(f, point, maxResults, caseSens, reload) if FileUtils.isJava(f.file) =>
      javaCompiler.askCompletionsAtPoint(f, point, maxResults, caseSens) pipeTo sender
    case CompletionsReq(fileInfo, point, maxResults, caseSens, reload) =>
      sender ! (scalaCompiler.map { cc =>
        val sourcefile = createSourceFile(cc, fileInfo)
        reporter.disable()
        val p = new OffsetPosition(sourcefile, point)
        cc.askCompletionsAt(p, maxResults, caseSens)
      }).getOrElse(VoidResponse)
    case UsesOfSymbolAtPointReq(file, point) =>
      sender ! (scalaCompiler.map { cc =>
        val p = pos(cc, file, point)
        cc.askLoadedTyped(p.source)
        val uses = cc.askUsesOfSymAtPoint(p)
        ERangePositions(uses.map(ERangePositionHelper.fromRangePosition))
      }).getOrElse(VoidResponse)
    case PackageMemberCompletionReq(path: String, prefix: String) =>
      sender ! (scalaCompiler.map { cc =>
        val members = cc.askCompletePackageMember(path, prefix)
        members
      }).getOrElse(VoidResponse)
    case InspectTypeAtPointReq(file: File, range: OffsetRange) =>
      sender ! (scalaCompiler.map { cc =>
        val p = pos(cc, file, range)
        cc.askLoadedTyped(p.source)
        cc.askInspectTypeAt(p)
      }).getOrElse(VoidResponse)
    case InspectTypeByIdReq(id: Int) =>
      sender ! (scalaCompiler.map { cc =>
        cc.askInspectTypeById(id)
      }).getOrElse(VoidResponse)
    case InspectTypeByNameReq(name: String) =>
      sender ! (scalaCompiler.map { cc =>
        cc.askInspectTypeByName(name)
      }).getOrElse(VoidResponse)
    case SymbolAtPointReq(file: File, point: Int) =>
      sender ! (scalaCompiler.map { cc =>
        val p = pos(cc, file, point)
        cc.askLoadedTyped(p.source)
        cc.askSymbolInfoAt(p)
      }).getOrElse(VoidResponse)
    case SymbolByNameReq(typeFullName: String, memberName: Option[String], signatureString: Option[String]) =>
      sender ! (scalaCompiler.map { cc =>
        cc.askSymbolByName(typeFullName, memberName, signatureString)
      }).getOrElse(VoidResponse)
    case DocUriAtPointReq(file: File, range: OffsetRange) if FileUtils.isJava(file) =>
      javaCompiler.askDocSignatureAtPoint(SourceFileInfo(file, None, None), range.from) pipeTo sender
    case DocUriAtPointReq(file: File, range: OffsetRange) =>
      sender ! (scalaCompiler.map { cc =>
        val p = pos(cc, file, range)
        cc.askLoadedTyped(p.source)
        cc.askDocSignatureAtPoint(p)
      }).getOrElse(VoidResponse)
    case DocUriForSymbolReq(typeFullName: String, memberName: Option[String], signatureString: Option[String]) =>
      sender ! (scalaCompiler.map { cc =>
        cc.askDocSignatureForSymbol(typeFullName, memberName, signatureString)
      }).getOrElse(VoidResponse)
    case InspectPackageByPathReq(path: String) =>
      sender ! (scalaCompiler.map { cc =>
        cc.askPackageByPath(path)
      }).getOrElse(VoidResponse)
    case TypeAtPointReq(file: File, range: OffsetRange) if FileUtils.isJava(file) =>
      javaCompiler.askTypeAtPoint(SourceFileInfo(file, None, None), range.from) pipeTo sender
    case TypeAtPointReq(file: File, range: OffsetRange) =>
      sender ! (scalaCompiler.map { cc =>
        val p = pos(cc, file, range)
        cc.askLoadedTyped(p.source)
        cc.askTypeInfoAt(p)
      }).getOrElse(VoidResponse)
    case TypeByIdReq(id: Int) =>
      sender ! (scalaCompiler.map { cc =>
        cc.askTypeInfoById(id)
      }).getOrElse(VoidResponse)
    case TypeByNameReq(name: String) =>
      sender ! (scalaCompiler.map { cc =>
        cc.askTypeInfoByName(name)
      }).getOrElse(VoidResponse)
    case TypeByNameAtPointReq(name: String, file: File, range: OffsetRange) =>
      sender ! (scalaCompiler.map { cc =>
        val p = pos(cc, file, range)
        cc.askLoadedTyped(p.source)
        cc.askTypeInfoByNameAt(name, p)
      }).getOrElse(VoidResponse)
    case CallCompletionReq(id: Int) =>
      sender ! (scalaCompiler.map { cc =>
        cc.askCallCompletionInfoById(id)
      }).getOrElse(VoidResponse)
    case SymbolDesignationsReq(f, start, end, tpes) if FileUtils.isJava(f) =>
      sender ! SymbolDesignations(f, List.empty)
    case SymbolDesignationsReq(f, start, end, tpes) =>
      sender ! (scalaCompiler.map { cc =>
        val sf = createSourceFile(cc, f)
        if (tpes.nonEmpty) {
          val clampedEnd = math.max(end, start)
          val pos = new RangePosition(sf, start, start, clampedEnd)
          cc.askLoadedTyped(pos.source)
          cc.askSymbolDesignationsInRegion(pos, tpes)
        } else {
          SymbolDesignations(File(sf.path), List.empty)
        }
      }).getOrElse(VoidResponse)
    case ImplicitInfoReq(file: File, range: OffsetRange) =>
      sender() ! (scalaCompiler.map { cc =>
        val p = pos(cc, file, range)
        cc.askLoadedTyped(p.source)
        cc.askImplicitInfoInRegion(p)
      }).getOrElse(VoidResponse)
    case ExpandSelectionReq(file, start: Int, stop: Int) =>
      sender ! handleExpandselection(file, start, stop)
    case FormatSourceReq(files: List[File]) =>
      sender ! (scalaCompiler.map { cc =>
        handleFormatFiles(files)
        VoidResponse
      }).getOrElse(VoidResponse)
    case FormatOneSourceReq(fileInfo: SourceFileInfo) =>
      sender ! (scalaCompiler.map { cc =>
        StringResponse(handleFormatFile(fileInfo))
      }).getOrElse(VoidResponse)
  }

  def handleReloadFiles(files: List[SourceFileInfo]): RpcResponse = {
    val missingFiles = files.filterNot(_.file.exists())
    if (missingFiles.nonEmpty) {
      val missingFilePaths = missingFiles.map { f => "\"" + f.file + "\"" }.mkString(",")
      EnsimeServerError(s"file(s): $missingFilePaths do not exist")
    } else {

      val (javas, scalas) = files.filter(_.file.exists).partition(
        _.file.getName.endsWith(".java")
      )

      if (scalas.nonEmpty) {
        for (cc <- scalaCompiler) {
          val sourceFiles = scalas.map { f => createSourceFile(cc, f) }
          cc.askReloadFiles(sourceFiles)
          cc.askNotifyWhenReady()
        }
      }
      if (javas.nonEmpty) {
        javaCompiler.askTypecheckFiles(javas)
      }
      VoidResponse
    }
  }

  def pos(cc: RichCompilerControl, file: File, range: OffsetRange): OffsetPosition = {
    val f = cc.createSourceFile(file.canon.getPath)
    if (range.from == range.to) new OffsetPosition(f, range.from)
    else new RangePosition(f, range.from, range.from, range.to)
  }

  def pos(cc: RichCompilerControl, file: File, offset: Int): OffsetPosition = {
    val f = cc.createSourceFile(file.canon.getPath)
    new OffsetPosition(f, offset)
  }

  def createSourceFile(cc: RichCompilerControl, file: File): SourceFile = {
    cc.createSourceFile(file.canon.getPath)
  }

  def createSourceFile(cc: RichCompilerControl, file: SourceFileInfo): SourceFile = {
    cc.createSourceFile(file)
  }

}
object Analyzer {
  def apply(
    broadcaster: ActorRef,
    indexer: ActorRef,
    search: SearchService
  )(
    implicit
    config: EnsimeConfig,
    vfs: EnsimeVFS
  ) = Props(new Analyzer(broadcaster, indexer, search, config, vfs))
}
