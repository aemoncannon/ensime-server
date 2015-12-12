package org.ensime.core.javac

import com.sun.source.tree.Tree
import com.sun.source.util.TreePath
import javax.lang.model.`type`.{ DeclaredType, PrimitiveType, TypeKind, TypeMirror }
import javax.lang.model.element.{ Element, TypeElement }

trait Helpers {

  def typeMirror(info: CompilationInfo, t: Tree): Option[TypeMirror] = {
    Option(info.getTrees().getTypeMirror(info.getTrees().getPath(info.getCompilationUnit(), t)))
  }

  def typeElement(info: CompilationInfo, t: Tree): Option[Element] = {
    typeMirror(info, t).map(info.getTypes().asElement)
  }

  def fqn(info: CompilationInfo, p: TreePath): Option[(String, String)] = {
    val tm = Option(info.getTrees().getTypeMirror(p))
    tm.flatMap { tm => fqn(info, tm) }
  }

  def fqn(info: CompilationInfo, t: Tree): Option[(String, String)] = {
    Option(info.getTrees().getPath(info.getCompilationUnit(), t)).flatMap { p => fqn(info, p) }
  }

  def fqn(info: CompilationInfo, tm: TypeMirror): Option[(String, String)] = {

    def parseFqn(qualifiedName: String) = {
      val (front, back) = qualifiedName.split("\\.").partition { s => s.forall(Character.isLowerCase) }
      (front.mkString("."), back.mkString("."))
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
      case tm: PrimitiveType if tm.getKind.isPrimitive => Some(("", tm.toString))
      case _ => None
    }
  }
}
