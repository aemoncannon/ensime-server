package org.ensime.core

import java.io.File

import akka.event.slf4j.SLF4JLogging
import org.ensime.api.OffsetSourcePosition
import org.ensime.api.LineSourcePosition
import org.ensime.api.SourceFileInfo
import org.ensime.core.javac.JavaCompiler
import org.ensime.fixture._
import org.ensime.indexer.EnsimeVFS
import org.ensime.indexer.SearchServiceTestUtils
import org.scalatest._
import scala.concurrent.Await
import scala.concurrent.duration.Duration

class JavaCompilerSpec extends FlatSpec with Matchers
    with IsolatedJavaCompilerFixture
    with SearchServiceTestUtils
    with SLF4JLogging {

  val original = EnsimeConfigFixture.SimpleTestProject

  "JavaCompiler" should "generate compilation notes" in withJavaCompiler { (_, config, cc, store, search) =>
    runForPositionInCompiledSource(config, cc,
      "import java.io.File;",
      "class Test1 {",
      "  ksjdfkdjsf @1@",
      "}") { (sf, p, label, cc) =>
      }
    assert(!(store.notes.isEmpty))
  }

  it should "find type at point" in withJavaCompiler { (_, config, cc, store, search) =>
    runForPositionInCompiledSource(config, cc,
      "import java.io.File;",
      "class Tes@0@t1 {",
      "  private void main() {",
      "    int fo@1@o = 1;",
      "    System.out.println(fo@2@o);",
      "  }",
      "}") { (sf, offset, label, cc) =>
        val info = cc.askTypeAtPoint(sf, offset).get
        label match {
          case "0" => info.name shouldBe "Test1"
          case "1" => info.name shouldBe "int"
          case "2" => info.name shouldBe "int"
        }
      }
  }

  it should "link symbols to their source positions" in withJavaCompiler { (_, config, cc, store, _) =>

    val test1 = SourceFileInfo(new File(config.rootDir, "testing/simple/src/main/java/org/example/Test1.java"))
    val test2 = SourceFileInfo(new File(config.rootDir, "testing/simple/src/main/java/org/example/Test2.java"))

    cc.askLinkPos("org.example.Test2", test2) should matchPattern { case Some(OffsetSourcePosition(f, 22)) => }
    cc.askLinkPos("org.example.Foo", test2) should matchPattern { case None => }
    cc.askLinkPos("org.example.Test2.Bar", test2) should matchPattern { case Some(OffsetSourcePosition(f, 260)) => }
//    cc.askLinkPos("org.example.Test2.compute()", test2) should matchPattern { case Some(OffsetSourcePosition(f, 58)) => }

  }

  it should "find symbol at point" in withJavaCompiler { (_, config, cc, store, search) =>
    implicit val searchService = search
    refresh()

    runForPositionInCompiledSource(config, cc,
      "package org.example;",
      "import java.io.File;",
      "class Test1 {",
      "  private class Foo { public Foo() {} }",
      "  private void main(String[] args) {",
      "    int foo = 1;",
      "    System.out.println(fo@0@o);",
      "    System.out.println(ar@1@gs);",
      "    System.out.pr@3@intln(new Fo@2@o());",
      "    System.out.println(new Fi@4@le(\".\"));",
      "    System.out.println(Tes@5@t2.com@6@pute());",
      "  }",
      "}") { (sf, offset, label, cc) =>
        val info = cc.askSymbolAtPoint(sf, offset).get
        label match {
          case "0" =>
            info.name shouldBe "foo"
            info.`type`.name shouldBe "int"
            info.isCallable shouldBe false
          case "1" =>
            info.name shouldBe "args"
            info.`type`.name shouldBe "java.lang.String[]"
            info.isCallable shouldBe false
          case "2" =>
            info.name shouldBe "Foo"
            info.`type`.name shouldBe "org.example.Test1.Foo"
            info.isCallable shouldBe false
            info.declPos should matchPattern { case Some(OffsetSourcePosition(f, 58)) if f.getName == "Test1.java" => }
          case "3" =>
            info.name shouldBe "println"
            info.`type`.name shouldBe "(java.lang.Object)void"
            info.isCallable shouldBe true
          case "4" =>
            info.name shouldBe "File"
            info.`type`.name shouldBe "java.io.File"
            info.isCallable shouldBe false
          case "5" =>
            info.name shouldBe "Test2"
            info.`type`.name shouldBe "org.example.Test2"
            info.isCallable shouldBe false
            info.declPos should matchPattern { case Some(OffsetSourcePosition(f, 22)) if f.getName == "Test2.java" => }
          case "6" =>
            info.name shouldBe "compute"
            info.`type`.name shouldBe "()int"
            info.isCallable shouldBe true
            // NOTE: we should find an OffsetSourcePosition here as the source enters
            // the compiler's working set in case "5" above.
            // TODO - However if the 'element' is not found, we'll fall through to indexer lookup.
            // look into more exhaustive ways of finding the element.
            info.declPos should matchPattern {
              case Some(LineSourcePosition(f, 8)) if f.getName == "Test2.java" =>
              case Some(OffsetSourcePosition(f, 48)) if f.getName == "Test2.java" =>
            }
        }
      }
  }

  it should "find completions at point" in withJavaCompiler { (_, config, cc, store, search) =>
    runForPositionInCompiledSource(config, cc,
      "import java.io.File;",
      "import java.lang.Str@5@;",
      "import java.util.Map.E@6@;",
      "import java.util.Map.E@7@blablabla;",
      "class Test1 {",
      "  public static final int MAX_VALUE = 10;",
      "  public static class TestInner {",
      "    public int maxValue = 10;",
      "    private void main(String foo, String bar) {",
      "      File f = new File();",
      "      f.toSt@0@;",
      "      System.out.println(f.toStr@1@);",
      "      System.out.println((f).toStr@2@);",
      "      System.out.println(f.toString().substr@3@);",
      "      f.@4@;",
      "      new Fi@8@",
      "      System.out.println(fo@9@ + bar);",
      "      System.out.println(maxV@10@);",
      "      System.out.println(MAX_@11@);",
      "      System.out.println(new Inte@12@);",
      "      int testinner = 5;",
      "      System.out.println(f.toStr@1@);",
      "      System.out.@14@",
      "    }",
      "  }",
      "}") { (sf, offset, label, cc) =>
        val info = cc.askCompletionsAtPoint(sf, offset, 0, false)
        label match {
          case "0" => assert(info.completions.exists(_.name == "toString"))
          case "1" => assert(info.completions.exists(_.name == "toString"))
          case "2" => assert(info.completions.exists(_.name == "toString"))
          case "3" => assert(info.completions.exists(_.name == "substring"))
          case "4" => assert(info.completions.exists(_.name == "createTempFile") &&
            info.completions.exists(_.name == "wait"))
          case "5" => assert(info.completions.exists(_.name == "String"))
          case "6" => assert(info.completions.exists(_.name == "Entry"))
          case "7" => assert(info.completions.exists(_.name == "Entry"))
          case "8" => assert(info.completions.exists(_.name == "File"))
          case "9" => assert(info.completions.exists(_.name == "foo"))
          case "10" => assert(info.completions.exists(_.name == "maxValue"))
          case "11" => assert(info.completions.exists(_.name == "MAX_VALUE"))
          case "12" => assert(info.completions.exists(_.name == "Integer"))

          case "13" =>
            // exact matches should be preferred
            assert(info.completions(0).name == "TestInner")
            assert(info.completions(1).name == "testinner")

          case "14" => assert(info.completions.exists(_.name == "println"))
        }
      }
  }

  it should "find completion at beginning of file" in withJavaCompiler { (_, config, cc, store, search) =>
    runForPositionInCompiledSource(config, cc, "Sys@0@") { (sf, offset, label, cc) =>
      val info = cc.askCompletionsAtPoint(sf, offset, 0, false)
      label match {
        case "0" => assert(info.completions.exists(_.name == "System"))
      }
    }
  }

  it should "find doc sig at point" in withJavaCompiler { (_, config, cc, store, search) =>
    runForPositionInCompiledSource(config, cc,
      "import java.io.Fi@5@le;",
      "class Test1 {",
      "  private void main() {",
      "    File f = new F@1@ile(\".\")",
      "    System.out.println(f.toStr@2@ing());",
      "    File.create@3@TempFile(\"bla\", \"foo\");",
      "    File.create@4@TempFile(\"bla\", \"foo\", f);",
      "    System.out.println(\"bla\".ind@6@exOf(\"b\"));",
      "    System.out.println(\"bla\".index@7@Of(\"b\", 1));",
      "    System.out.println(\"bla\".index@8@Of(1));",
      "  }",
      "}") { (sf, offset, label, cc) =>
        val sig = cc.askDocSignatureAtPoint(sf, offset).get.java
        label match {
          case "0" => sig.fqn shouldBe DocFqn("", "Test1")
          case "1" => sig.fqn shouldBe DocFqn("java.io", "File")
          case "2" => sig shouldBe DocSig(DocFqn("java.io", "File"), Some("toString()"));
          case "3" => sig shouldBe DocSig(DocFqn("java.io", "File"), Some("createTempFile(java.lang.String,java.lang.String)"));
          case "4" => sig shouldBe DocSig(DocFqn("java.io", "File"), Some("createTempFile(java.lang.String,java.lang.String,java.io.File)"));
          case "5" => sig.fqn shouldBe DocFqn("java.io", "File")
          case "6" => sig shouldBe DocSig(DocFqn("java.lang", "String"), Some("indexOf(java.lang.String)"));
          case "7" => sig shouldBe DocSig(DocFqn("java.lang", "String"), Some("indexOf(java.lang.String,int)"));
          case "8" => sig shouldBe DocSig(DocFqn("java.lang", "String"), Some("indexOf(int)"));
        }
      }
  }

}
