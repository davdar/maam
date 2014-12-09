package notjs.tester

import java.io.{File, FileFilter}
import org.scalatest.FunSuite

object JSFilter extends FileFilter {
  def accept(file: File): Boolean =
    file.getName.endsWith(".js")
}

object TestBase {
  val PRINT_TEST_NAME = false
}

abstract class TestBase(val testdirs: Seq[String]) extends FunSuite {
  // merely constructing this causes tests to be run.  This behvaior should be
  // changed if subclasses have non-empty constructors
  runtests()

  def runtest(file: File): Unit

  def customTest(name: String)(runTest: => Unit) {
    test(name) {
      if (TestBase.PRINT_TEST_NAME) println(name)
      runTest
    }
  }

  def testNameBase(file: File): String =
    file.getPath.toString

  def runtests() {
    testdirs.foreach(dir => {
      val dirFile = new File(dir)
      if (!dirFile.isDirectory) {
        sys.error(dir + " is not a directory!")
      }
      
      dirFile.listFiles(JSFilter).foreach(runtest)
    })
  }
}                
