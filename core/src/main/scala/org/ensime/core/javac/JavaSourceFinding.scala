package org.ensime.core.javac

import akka.event.slf4j.SLF4JLogging
import com.sun.source.tree.{ MemberSelectTree, Tree }
import com.sun.source.util.TreePath
import java.io.File
import javax.lang.model.element.Element
import org.ensime.api._
import org.ensime.model.LineSourcePositionHelper

trait JavaSourceFinding extends SLF4JLogging { self: JavaCompiler =>

  protected def findInCompiledUnit(info: CompilationInfo, fqn: String): Option[SourcePosition] = {
    Option(info.getElements().getTypeElement(fqn)).flatMap(elementPosition(info, _))
  }

  private def elementPosition(info: CompilationInfo, el: Element): Option[SourcePosition] = {
    // if we can get a tree for the element, determining start position
    // is easy
    Option(info.getTrees.getPath(el)).map { path =>
      OffsetSourcePosition(
        new File(path.getCompilationUnit.getSourceFile.getName),
        info.getTrees.getSourcePositions
          .getStartPosition(path.getCompilationUnit, path.getLeaf).toInt
      )
    }
  }

  protected def findDeclPos(info: CompilationInfo, path: TreePath): Option[SourcePosition] = {
    val tpeMirror = Option(info.getTrees().getTypeMirror(path))
    // TODO behavior of Element discovery seems to vary between jvm versions.
    val element =
      tpeMirror.flatMap { tm => Option(info.getTypes.asElement(tm)) }
        .orElse(Option(info.getTrees.getElement(path)))
    element.flatMap(elementPosition(info, _)).orElse(findInIndexer(info, path))
  }

  private def findInIndexer(info: CompilationInfo, path: TreePath): Option[SourcePosition] = {
    def indexerName(t: Tree): String = t match {
      case t: MemberSelectTree =>
        indexerName(t.getExpression) + "." + t.getIdentifier.toString
      case _ => fqn(info, t).map(_.productIterator.mkString(".")).getOrElse("NA")
    }
    val query = indexerName(path.getLeaf)
    val hit = search.findUnique(query)
    log.debug(s"search: $query = $hit")
    hit.flatMap(LineSourcePositionHelper.fromFqnSymbol(_)(config, vfs)).flatMap { sourcePos =>
      if (sourcePos.file.getName.endsWith(".java") && sourcePos.file.exists)
        askLinkPos(query, SourceFileInfo(sourcePos.file, None, None)).orElse(Some(sourcePos))
      else
        Some(sourcePos)
    }
  }

}

