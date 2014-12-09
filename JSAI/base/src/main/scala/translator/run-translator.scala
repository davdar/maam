package notjs.translator

import org.mozilla.javascript.ast.{AstNode => RhinoAST, AstRoot}

import notjs.syntax.{Seq => SyntaxSeq, _}
import notjs.translator.jsast._
import notjs.translator.notjspass.TransformNotJSAST
import org.mozilla.javascript._


import java.io._

object RunTranslator {
  def translateFileToProgram(file: File, debug: Boolean): Stmt = 
    translateAST(parseJavaScript(file), debug)

  def translateAST(node: RhinoAST, debug: Boolean): Stmt = {
    PVarMapper.reset()
    TransformNotJSAST(
      Translator(
	TransformJSAST(
	  RhinoToJSAST(node, debug)))).asInstanceOf[Stmt]
  }

  def parseJavaScript(file: File): AstRoot = {
    val reader = new FileReader(file)
    try {
      new Parser().parse(reader, file.getCanonicalPath, 1)
    } finally {
      reader.close()
    }
  }

  def main(args: Array[String]) {
    println(translateFileToProgram(new File(args(0)), args.toSet("--debug")))
    println(PVarMapper.getMapping.toList.sortWith(_._1 < _._1))
  }
}

