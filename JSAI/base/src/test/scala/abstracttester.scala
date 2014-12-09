package notjs.tester.abstracted

import notjs.tester._
import java.io.File
import org.scalatest.FunSuite
import notjs.concrete
import notjs.abstracted
import notjs.abstracted.{domains ⇒ adomains}
import notjs.concrete.{domains ⇒ cdomains}
import sys.process._

abstract class AbstractTestParent(testdirs: Seq[String], val options: Seq[Seq[String]] = Seq(Seq())) extends TestBase(testdirs) {
  import TestHelpers._
  
  def testName(file: File, opts: Seq[String]): String = {
    val optionsStr = 
      " with options: " + (if (opts.isEmpty) "None" else opts.mkString(", "))
    testNameBase(file) + optionsStr
  }

  def runtest(file: File) {
    options.foreach(opts => {
      customTest(testName(file, opts)) {
        val fname = file.getAbsolutePath
        val cmap = concrete.interpreter.notJS.runner(Array(fname, "--testing", "--catchexc"))
        val amap = abstracted.interpreter.notJS.runner(Array(fname, "--testing", "--catchexc") ++ opts)

        // Tests should be written so that they do not produce empty output
        // Empty outputs are considered fails
        assert(cmap.size > 0, "Concrete interpreter produces empty output")
        assert(amap.size > 0, "Abstract interpreter produces empty output")
        // for every output in concrete, there should be a corresponding output in abstract
        assert((cmap.keySet -- amap.keySet).isEmpty, "Unsound: Abstract interpreter does not reach all prints that concrete interpreter reaches")
        // check for over approximation
        val sound = cmap.forall((t) ⇒ {
          t._2.forall((c) ⇒ amap(t._1).exists(a ⇒ overapproximates(a, c)))
        })
        assert(sound, "Unsound: Abstract interpreter does not soundly approximate concrete interpreter")
      }
    })
  }
}

class SimpleTests extends AbstractTestParent(
  Seq(
    "src/test/resources/base/",
    "src/test/resources/scoping/",
    "src/test/resources/init/"
  ))

class SimpleTestsWithOptions extends AbstractTestParent(
  Seq("src/test/resources/base/",
      "src/test/resources/scoping/",
      "src/test/resources/init/"),
  Seq(Seq("--prune"),
      Seq("--lightgc"),
      Seq("--fullgc"),
      Seq("--prune", "--lightgc"),
      Seq("--prune", "--fullgc")))

class SimpleTestsWithTraces extends AbstractTestParent(
  Seq("src/test/resources/base/",
      "src/test/resources/scoping/",
      "src/test/resources/init/"),
  Seq(Seq("--trace=fs"),
      Seq("--trace=stack-2-1"),
      Seq("--trace=acyclic-1"),
      Seq("--trace=obj-2-1"),
      Seq("--trace=cxo-2-1-2-1"),
      Seq("--trace=cno-2-1")))


