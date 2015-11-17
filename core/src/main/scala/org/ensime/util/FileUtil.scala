package org.ensime.util

import java.io._
import java.net.URI
import java.nio.charset.Charset

import org.apache.commons.vfs2.FileObject

import scala.collection.mutable
import scala.reflect.internal.util.{ BatchSourceFile, SourceFile }

import org.ensime.api._
import org.ensime.util.file._

/**
 *  Wrap BatchSourceFile to allow access to only the (String, Array[Char])
 *  constructor, which creates an in-memory source file.
 */
class InMemorySourceFile(path: String, content: Seq[Char])
  extends BatchSourceFile(path, content.toArray) {}

object RichFileObject {
  implicit class RichFileObject(val fo: FileObject) extends AnyVal {
    // None if the fo is not an entry in an archive
    def pathWithinArchive: Option[String] = {
      val uri = fo.getName.getURI
      if (uri.startsWith("jar") || uri.startsWith("zip"))
        Some(fo.getName.getRoot.getRelativeName(fo.getName))
      else None
    }

    // assumes it is a local file
    def asLocalFile: File = {
      require(fo.getName.getURI.startsWith("file"))
      new File(new URI(fo.getName.getURI))
    }
  }
}

object FileUtils {

  def exists(f: SourceFileInfo) = f match {
    case SourceFileInfo(f, _, _) if f.exists() => true
    case SourceFileInfo(_, Some(c), _) => true
    case SourceFileInfo(_, _, Some(f)) if f.exists() => true
    case _ => false
  }

  // prefer file.readString()
  def readFile(f: File, cs: Charset): Either[IOException, String] =
    try Right(f.readString()(cs))
    catch {
      case e: IOException => Left(e)
    }

  def writeChanges(changes: List[FileEdit], cs: Charset): Either[Exception, List[File]] = {
    val editsByFile = changes.collect { case ed: TextEdit => ed }.groupBy(_.file)
    val newFiles = changes.collect { case ed: NewFile => ed }
    try {
      val rewriteList = newFiles.map { ed => (ed.file, ed.text) } ++
        editsByFile.map {
          case (file, fileChanges) =>
            readFile(file, cs) match {
              case Right(contents) =>
                val newContents = FileEditHelper.applyEdits(fileChanges.toList, contents)
                (file, newContents)
              case Left(e) => throw e
            }
        }

      val deleteFiles = changes.collect { case ed: DeleteFile => ed }
      for (ed <- deleteFiles) {
        ed.file.delete()
      }

      Right(
        for {
          (file, contents) <- rewriteList
        } yield {
          file.writeString(contents)(cs)
          file
        }
      )
    } catch {
      case e: Exception => Left(e)
    }
  }

}
