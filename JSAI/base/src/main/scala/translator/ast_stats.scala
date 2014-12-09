package notjs.translator

import notjs.syntax._
import scala.collection.JavaConverters._
import java.io._
import org.mozilla.javascript._
import org.mozilla.javascript.ast.{Jump => RhinoJump, AstNode => RhinoAST,
				   Scope => RhinoScope, _}

// gets statistics for both Rhino and notJS nodes
object AstStats {
  def numRhinoNodes(ast: RhinoAST): Int = {
    import java.util.{List => JList}

    def rs(asts: RhinoAST*): Int =
      asts.map(r).sum

    def rl[T <: RhinoAST](asts: JList[T]): Int =
      Option(asts).map(l => rs(l.asScala.toSeq: _*)).getOrElse(0)

    def rNode(node: Node): Int =
      node match {
	case a: RhinoAST => r(a)
	case _ => 0
      }

    def r(ast: RhinoAST): Int = {
      1 + (ast match {
	case b: Block =>
	  b.asScala.map(rNode).sum
	case w: WithStatement => 
	  rs(w.getExpression, w.getStatement)
	case w: WhileLoop =>
	  rs(w.getCondition, w.getBody)
	case d: DoLoop =>
	  rs(d.getCondition, d.getBody)
	case vd: VariableDeclaration =>
	  vd.getVariables.asScala.map(initializer =>
	    r(initializer.getTarget) + Option(initializer.getInitializer).map(r).getOrElse(0)).sum
	case f: ForInLoop =>
	  rs(f.getIteratedObject, f.getBody)
	case f: ForLoop =>
	  rs(f.getInitializer, f.getCondition, f.getIncrement, f.getBody)
	case t: ThrowStatement =>
	  r(t.getExpression)
	case l: LabeledStatement =>
	  r(l.getStatement)
	case _: BreakStatement | _: ContinueStatement => 0
	case ret: ReturnStatement =>
	  Option(ret.getReturnValue).map(r).getOrElse(0)
	case f: FunctionNode =>
	  r(f.getFunctionName) + rl(f.getFunctions) + rl(f.getParams) + r(f.getBody)
	case s: SwitchStatement =>
	  r(s.getExpression) + rl(s.getCases)
	case s: SwitchCase =>
	  rl(s.getStatements) + Option(s.getExpression).map(r).getOrElse(0)
	case c: IfStatement =>
	  r(c.getCondition) + r(c.getThenPart) + Option(c.getElsePart).map(r).getOrElse(0)
	case _: NumberLiteral | _: StringLiteral | _: KeywordLiteral | _: Name => 0
	case p: ParenthesizedExpression =>
	  r(p.getExpression)
	case t: TryStatement =>
	  r(t.getTryBlock) + rl(t.getCatchClauses) + Option(t.getFinallyBlock).map(r).getOrElse(0)
	case c: CatchClause =>
	  r(c.getBody) + r(c.getCatchCondition) + r(c.getVarName)
	case a: Assignment =>
	  r(a.getLeft) + r(a.getRight)
	case _: RegExpLiteral => 0
	case c: ConditionalExpression =>
	  r(c.getTestExpression) + r(c.getTrueExpression) + r(c.getFalseExpression)
	case p: PropertyGet =>
	  r(p.getTarget) + r(p.getProperty)
	case e: ElementGet =>
	  r(e.getTarget) + r(e.getElement)
	case f: FunctionCall =>
	  // NewExpression is a subclass of FunctionCall
	  r(f.getTarget) + rl(f.getArguments)
	case n: InfixExpression =>
	  r(n.getLeft) + r(n.getRight)
	case u: UnaryExpression =>
	  r(u.getOperand)
	case o: ObjectLiteral =>
	  rl(o.getElements)
	case a: ArrayLiteral =>
	  rl(a.getElements)
	case a: AstRoot =>
	  rl(a.getStatements)
	case e: ExpressionStatement =>
	  r(e.getExpression)
	case _: EmptyExpression => 0
	case s: RhinoScope =>
	  s.asScala.map(rNode).sum
	case null => 0
      })
    }
    r(ast) + 1
  }
  
  def numNotJSNodes(ast: AST): Int = {
    def rs(asts: AST*): Int =
      asts.map(r).sum

    def r(ast: AST): Int =
      1 + (ast match {
	case Decl(bind, s) =>
	  bind.map( { case (v, e) => rs(v, e) } ).sum + r(s)
	case SDecl(_, s) =>
	  r(s)
	case Seq(ss) =>
	  rs(ss: _*)
	case If(e, s1, s2) =>
	  rs(e, s1, s2)
	case While(e, s) =>
	  rs(e, s)
	case Assign(x, e) =>
	  rs(x, e)
	case Call(x, e1, e2, e3) =>
	  rs(x, e1, e2, e3)
	case New(x, e1, e2) =>
	  rs(x, e1, e2)
	case Newfun(x, m, n) =>
	  rs(x, m, n)
	case ToObj(x, e) =>
	  rs(x, e)
	case Del(x, e1, e2) =>
	  rs(x, e1, e2)
	case Update(e1, e2, e3) =>
	  rs(e1, e2, e3)
	case Throw(e) =>
	  r(e)
	case Try(s1, x, s2, s3) =>
	  rs(s1, x, s2, s3)
	case Lbl(_, s) =>
	  r(s)
	case Jump(_, e) =>
	  r(e)
	case For(x, e, s) =>
	  rs(x, e, s)
	case Print(e) => 
	  r(e)
	case Binop(_, e1, e2) =>
	  rs(e1, e2)
	case Unop(_, e) =>
	  r(e)
	case Method(self, args, s) =>
	  rs(self, args, s)
	case Merge() | NumAST(_) | BoolAST(_) | StrAST(_) | UndefAST() | NullAST() | PVar(_) | Scratch(_) => 0
      })
    r(ast)
  }

  def main(args: Array[String]) {
    args.foreach(filename => {
      try {
	val rhinoAST = RunTranslator.parseJavaScript(new File(filename))
	val notJSAST = RunTranslator.translateAST(rhinoAST, false)
	println("Filename: " + filename)
	println("\tNumber of Rhino nodes: " + numRhinoNodes(rhinoAST))
	println("\tNumber of notJS nodes: " + numNotJSNodes(notJSAST))
      } catch {
	case e: Exception => {
	  println(e)
	  e.printStackTrace
	  println("Could not parse/translate '" + filename + "': " + e.getMessage)
	}
      }
    })
  }
}
