package org.ensime.core

import java.io.File

import akka.event.slf4j.SLF4JLogging
import org.ensime.core.javac.JavaCompiler
import org.ensime.fixture._
import org.ensime.indexer.EnsimeVFS
import org.scalatest._
import scala.concurrent.Await
import scala.concurrent.duration.Duration

class JavaCompilerSpec extends FlatSpec with Matchers
    with IsolatedJavaCompilerFixture
    with SLF4JLogging {

  val original = EnsimeConfigFixture.SimpleTestProject

  "JavaCompiler" should "generate compilation notes" in withJavaCompiler { (_, config, cc, store) =>
    runForPositionInCompiledSource(config, cc,
      "import java.io.File;",
      "class Test1 {",
      "  ksjdfkdjsf @1@",
      "}") { (sf, p, label, cc) =>
      }
    assert(!(store.notes.isEmpty))
  }

  "JavaCompiler" should "find type at point" in withJavaCompiler { (_, config, cc, store) =>
    runForPositionInCompiledSource(config, cc,
      "import java.io.File;",
      "class Tes@0@t1 {",
      "  private void main() {",
      "    int fo@1@o = 1;",
      "    System.out.println(fo@2@o);",
      "  }",
      "}") { (sf, offset, label, cc) =>
        val info = Await.result(cc.askTypeAtPoint(sf, offset), Duration.Inf).get
        label match {
          case "0" => info.name shouldBe "Test1"
          case "1" => info.name shouldBe "int"
          case "2" => info.name shouldBe "int"
        }
      }
  }

  "JavaCompiler" should "find completions at point" in withJavaCompiler { (_, config, cc, store) =>
    runForPositionInCompiledSource(config, cc,
      "import java.io.File;",
      "import java.lang.Str@5@;",
      "import java.util.Map.E@6@;",
      "import java.util.Map.E@7@blablabla;",
      "class Test1 {",
      "  public static final int MAX_VALUE = 10;",
      "  public static class TestInner {",
      "  public int maxValue = 10;",
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
      "    }",
      "  }",
      "}") { (sf, offset, label, cc) =>
        val info = Await.result(cc.askCompletionsAtPoint(sf, offset, 0, false), Duration.Inf)
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
        }
      }
  }

  "JavaCompiler" should "find doc sig at point" in withJavaCompiler { (_, config, cc, store) =>
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
        val sig = Await.result(cc.askDocSignatureAtPoint(sf, offset), Duration.Inf).get.java
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
