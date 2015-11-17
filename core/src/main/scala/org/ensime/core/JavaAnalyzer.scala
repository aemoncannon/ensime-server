package org.ensime.core

import akka.actor._
import akka.event.LoggingReceive.withLabel
import org.ensime.api._
import org.ensime.core.javac._
import org.ensime.indexer.EnsimeVFS
import org.ensime.util.ReportHandler

class JavaAnalyzer(
    broadcaster: ActorRef,
    implicit val config: EnsimeConfig,
    implicit val vfs: EnsimeVFS
) extends Actor with Stash with ActorLogging {

  protected var javaCompiler: JavaCompiler = _

  override def preStart(): Unit = {
    javaCompiler = new JavaCompiler(
      config,
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

    // JavaAnalyzer is always 'ready', but legacy clients expect to see
    // AnalyzerReady
    broadcaster ! Broadcaster.Persist(AnalyzerReadyEvent)
  }

  override def postStop(): Unit = {
    // no way to stop the java compiler
  }

  // TODO: create a sealed family of requests / responses just for Java usage
  override def receive = {
    case TypecheckFileReq(sfi) =>
      javaCompiler.askTypecheckFiles(sfi :: Nil)
      sender() ! VoidResponse

    case TypecheckFilesReq(files) =>
      javaCompiler.askTypecheckFiles(files)
      sender() ! VoidResponse

    case CompletionsReq(f, point, maxResults, caseSens, _) =>
      sender() ! javaCompiler.askCompletionsAtPoint(f, point, maxResults, caseSens)

    case DocUriAtPointReq(file, range) =>
      sender() ! javaCompiler.askDocSignatureAtPoint(file, range.from)

    case TypeAtPointReq(file, range) =>
      sender() ! javaCompiler.askTypeAtPoint(file, range.from)

    case SymbolDesignationsReq(f, start, end, tpes) =>
      // NOT IMPLEMENTED YET
      sender ! SymbolDesignations(f.file, Nil)
  }

}
object JavaAnalyzer {
  def apply(
    broadcaster: ActorRef
  )(
    implicit
    config: EnsimeConfig,
    vfs: EnsimeVFS
  ) = Props(new JavaAnalyzer(broadcaster, config, vfs))
}
