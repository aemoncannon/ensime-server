package org.ensime.core

import java.io.{ File => JFile }
import java.nio.charset.Charset

import akka.actor._
import akka.event.LoggingReceive.withLabel
import org.ensime.api._
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

  protected var scalaCompiler: RichCompilerControl = _

  override def preStart(): Unit = {
    val presCompLog = LoggerFactory.getLogger(classOf[Global])

    settings = new Settings(presCompLog.error)
    settings.YpresentationDebug.value = presCompLog.isTraceEnabled
    settings.YpresentationVerbose.value = presCompLog.isDebugEnabled
    settings.verbose.value = presCompLog.isDebugEnabled
    settings.usejavacp.value = false
    config.scalaLibrary match {
      case Some(scalaLib) => settings.bootclasspath.value = scalaLib.getAbsolutePath
      case None => log.warning("scala-library.jar not present, enabling Odersky mode")
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

    broadcaster ! SendBackgroundMessageEvent("Initializing Analyzer. Please wait...")

    scalaCompiler.askNotifyWhenReady()
    if (config.sourceMode) scalaCompiler.askReloadAllFiles()
  }

  protected def makeScalaCompiler() = new RichPresentationCompiler(
    config, settings, reporter, self, indexer, search
  )

  protected def restartCompiler(keepLoaded: Boolean): Unit = {
    log.warning("Restarting the Presentation Compiler")
    val files = scalaCompiler.loadedFiles
    scalaCompiler.askShutdown()
    scalaCompiler = makeScalaCompiler()
    if (keepLoaded) {
      scalaCompiler.askReloadFiles(files)
    }
    scalaCompiler.askNotifyWhenReady()
    broadcaster ! CompilerRestartedEvent
  }

  override def postStop(): Unit = {
    Try(scalaCompiler.askClearTypeCache())
    Try(scalaCompiler.askShutdown())
  }

  def charset: Charset = scalaCompiler.charset

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

  def allTheThings: PartialFunction[RpcAnalyserRequest, Unit] = {
    case RemoveFileReq(file: File) =>
      scalaCompiler.askRemoveDeleted(file)
      sender ! VoidResponse
    case TypecheckAllReq =>
      allFilesMode = true
      scalaCompiler.askRemoveAllDeleted()
      scalaCompiler.askReloadAllFiles()
      scalaCompiler.askNotifyWhenReady()
      sender ! VoidResponse
    case UnloadAllReq =>
      if (config.sourceMode) {
        log.info("in source mode, will reload all files")
        scalaCompiler.askRemoveAllDeleted()
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
      sender ! handleRefactorPrepareRequest(req)
    case req: ExecRefactorReq =>
      sender ! handleRefactorExec(req)
    case req: CancelRefactorReq =>
      sender ! handleRefactorCancel(req)
    case CompletionsReq(fileInfo, point, maxResults, caseSens, reload) =>
      val sourcefile = createSourceFile(fileInfo)
      reporter.disable()
      val p = new OffsetPosition(sourcefile, point)
      val info = scalaCompiler.askCompletionsAt(p, maxResults, caseSens)
      sender ! info
    case UsesOfSymbolAtPointReq(file, point) =>
      val p = pos(file, point)
      scalaCompiler.askLoadedTyped(p.source)
      val uses = scalaCompiler.askUsesOfSymAtPoint(p)
      sender ! ERangePositions(uses.map(ERangePositionHelper.fromRangePosition))
    case PackageMemberCompletionReq(path: String, prefix: String) =>
      val members = scalaCompiler.askCompletePackageMember(path, prefix)
      sender ! members
    case InspectTypeAtPointReq(file: File, range: OffsetRange) =>
      val p = pos(file, range)
      scalaCompiler.askLoadedTyped(p.source)
      sender ! scalaCompiler.askInspectTypeAt(p)
    case InspectTypeByIdReq(id: Int) =>
      sender ! scalaCompiler.askInspectTypeById(id)
    case InspectTypeByNameReq(name: String) =>
      sender ! scalaCompiler.askInspectTypeByName(name)
    case SymbolAtPointReq(file: File, point: Int) =>
      val p = pos(file, point)
      scalaCompiler.askLoadedTyped(p.source)
      sender ! scalaCompiler.askSymbolInfoAt(p)
    case SymbolByNameReq(typeFullName: String, memberName: Option[String], signatureString: Option[String]) =>
      sender ! scalaCompiler.askSymbolByName(typeFullName, memberName, signatureString)
    case DocUriAtPointReq(file: File, range: OffsetRange) =>
      val p = pos(file, range)
      scalaCompiler.askLoadedTyped(p.source)
      sender() ! scalaCompiler.askDocSignatureAtPoint(p)
    case DocUriForSymbolReq(typeFullName: String, memberName: Option[String], signatureString: Option[String]) =>
      sender() ! scalaCompiler.askDocSignatureForSymbol(typeFullName, memberName, signatureString)
    case InspectPackageByPathReq(path: String) =>
      sender ! scalaCompiler.askPackageByPath(path)
    case TypeAtPointReq(file: File, range: OffsetRange) =>
      val p = pos(file, range)
      scalaCompiler.askLoadedTyped(p.source)
      sender ! scalaCompiler.askTypeInfoAt(p)
    case TypeByIdReq(id: Int) =>
      sender ! scalaCompiler.askTypeInfoById(id)
    case TypeByNameReq(name: String) =>
      sender ! scalaCompiler.askTypeInfoByName(name)
    case TypeByNameAtPointReq(name: String, file: File, range: OffsetRange) =>
      val p = pos(file, range)
      scalaCompiler.askLoadedTyped(p.source)
      sender ! scalaCompiler.askTypeInfoByNameAt(name, p)
    case CallCompletionReq(id: Int) =>
      sender ! scalaCompiler.askCallCompletionInfoById(id)

    case SymbolDesignationsReq(f, start, end, Nil) =>
      sender ! SymbolDesignations(f, List.empty)
    case SymbolDesignationsReq(f, start, end, tpes) =>
      val sf = createSourceFile(f)
      val clampedEnd = math.max(end, start)
      val pos = new RangePosition(sf, start, start, clampedEnd)
      scalaCompiler.askLoadedTyped(pos.source)
      val syms = scalaCompiler.askSymbolDesignationsInRegion(pos, tpes)
      sender ! syms

    case ImplicitInfoReq(file: File, range: OffsetRange) =>
      val p = pos(file, range)
      scalaCompiler.askLoadedTyped(p.source)
      sender() ! scalaCompiler.askImplicitInfoInRegion(p)

    case ExpandSelectionReq(file, start: Int, stop: Int) =>
      sender ! handleExpandselection(file, start, stop)
    case FormatSourceReq(files: List[File]) =>
      handleFormatFiles(files)
      sender ! VoidResponse
    case FormatOneSourceReq(fileInfo: SourceFileInfo) =>
      sender ! StringResponse(handleFormatFile(fileInfo))

  }

  def handleReloadFiles(files: List[SourceFileInfo]): RpcResponse = {
    val (extant, missingFiles) = files.partition(FileUtils.exists)
    if (missingFiles.nonEmpty) {
      val missingFilePaths = missingFiles.map { f => "\"" + f.file + "\"" }.mkString(",")
      EnsimeServerError(s"file(s): $missingFilePaths do not exist")
    } else {
      if (extant.nonEmpty) {
        val sourceFiles = extant.map(createSourceFile)
        scalaCompiler.askReloadFiles(sourceFiles)
        scalaCompiler.askNotifyWhenReady()
      }
      VoidResponse
    }
  }

  def pos(file: File, range: OffsetRange): OffsetPosition = {
    val f = scalaCompiler.createSourceFile(file.canon.getPath)
    if (range.from == range.to) new OffsetPosition(f, range.from)
    else new RangePosition(f, range.from, range.from, range.to)
  }

  def pos(file: File, offset: Int): OffsetPosition = {
    val f = scalaCompiler.createSourceFile(file.canon.getPath)
    new OffsetPosition(f, offset)
  }

  def createSourceFile(file: File): SourceFile = {
    scalaCompiler.createSourceFile(file.canon.getPath)
  }

  def createSourceFile(file: SourceFileInfo): SourceFile = {
    scalaCompiler.createSourceFile(file)
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
