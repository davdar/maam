package notjs.syntax
import notjs.translator.RunTranslator
import notjs.translator.PVarMapper
import java.io._

object DotPrint {
  def main(args: Array[String]) {
    assert(args.length >= 2, "Needs atleast 2 arguments: input js file name and output dot file name")
    val ast = RunTranslator.translateFileToProgram(new File(args(0)), args.toSet("--debug"))
    val mapping = PVarMapper.getMapping
    writeDot(ast, mapping, args(1))
  }

  def writeDot(a: AST, reverseMapping: Map[Int, String], file: String) {
  val out = new PrintWriter(new BufferedWriter(new FileWriter(file)))

  def strId(node: AST) = node.id.toString
  
  def getStr(n: Int) = reverseMapping(n)

  def outputBinding(binding: Tuple2[PVar,Exp]): String = {
    val bindid = output(binding._1)
    val expid = output(binding._2)

    printEdges(bindid, List(expid))
    bindid
  }

  def matchVar(n: Int): String = n match {
    case 0 => "user global (var 0)"
    case 1 => "global (var 1)"
    case 2 => "dummy (var 2)"
    case 3 => "Array (var 3)"
    case 4 => "Function (var 4)"
    case 5 => "String (var 5)"
    case 6 => "Regexp (var 6)"
    case 7 => "Boolean (var 7)"
    case 8 => "Number (var 8)"
    case 9 => "Date (var 9)"
    case 10 => "Error (var 10)"
    case 11 => "Arguments (var 11)"
    case 12 => "Object (var 12)"
    case 13 => "window.dummyAddress (var 13)"
    case _ => "Var: " + PVarMapper.getName(n)
  }

  def matchBop(b: Bop): String = b match {
    case ⌜+⌝ => "add"
    case ⌜−⌝ => "sub"
    case ⌜×⌝ => "mul"
    case ⌜÷⌝ => "div"
    case ⌜%⌝ => "mod"
    case ⌜<<⌝ => "lsh"
    case ⌜>>⌝ => "rsh"
    case ⌜>>>⌝ => "ursh"
    case ⌜<⌝ => "lt"
    case ⌜≤⌝ => "lte"
    case ⌜&⌝ => "band"
    case ⌜|⌝ => "bor"
    case ⌜⊻⌝ => "xor"
    case ⌜&&⌝ => "land"
    case ⌜||⌝ => "lor"
    case ⌜++⌝ => "cat"
    case ⌜≺⌝ => "lex"
    case ⌜≼⌝ => "lexe"
    case ⌜≈⌝ => "nse"
    case ⌜≡⌝ => "se"
    case ⌜⋆⌝ => "acc"
    case InstanceOf => "iof"
    case In => "in"
  }
  
  def matchUop(u: Uop): String = u match {
    case ⌞−⌟ => "nneg"
    case ⌞~⌟ => "bneg"
    case ⌞¬⌟ => "lneg"
    case Typeof => "typeof"
    case ToBool => "tobool"
    case IsPrim => "isprim"
    case ToStr => "tostr"
    case ToNum => "tonum"
  }

  def printNode(id: String, label: String) {
    out.print(id + " [label=\""+ label + "\\nID: "+id+"\"];")
  }

  def printEdges(id: String, lbls: List[String]) {
    lbls foreach ((lbl) => { out.println(id + " -> \"" + lbl + "\"") })
  }

  def output(node: AST): String = {
    val myid = strId(node)

    node match {
      case Decl(bind,s) => {
	val bindingIDs = bind map outputBinding
	val sid = output(s)

	printNode(myid, "Decl")
	printEdges(myid, bindingIDs ++ List(sid))
	myid
      }

      case SDecl(i, s) => {
	val sid = output(s)

	printNode(myid, "SDecl (" + i + ")")
	printEdges(myid, List(sid))
	myid
      }

      case Seq(ss) => {
	val ids = ss map output

	printNode(myid, "Seq")
	printEdges(myid, ids)
	myid
      }

      case If(e,s1,s2) => {
	val eid = output(e)
	val s1id = output(s1)
	val s2id = output(s2)

	printNode(myid, "If")
	printEdges(myid, List(eid, s1id, s2id))
	myid
      }

      case While(e, s) => {
	val eid = output(e)
	val sid = output(s)

	printNode(myid, "While")
	printEdges(myid, List(eid,sid))
	myid
      }

      case Assign(x, e) => {
	val xid = output(x)
	val eid = output(e)

	printNode(myid, "Assign")
	printEdges(myid, List(xid,eid))
	myid
      }

      case Call(x,e1,e2,e3) => {
	val xid = output(x)
	val e1id = output(e1)
	val e2id = output(e2)
	val e3id = output(e3)

	printNode(myid, "Call")
	printEdges(myid, List(xid,e1id,e2id,e3id))
	myid
      }

      case New(x,e1,e2) => {
	val xid = output(x)
	val e1id = output(e1)
	val e2id = output(e2)

	printNode(myid, "New")
	printEdges(myid, List(xid, e1id, e2id))
	myid
      }

      case Newfun(x,m,n) => {
	val xid = output(x)
	val mid = output(m)
	val nid = output(n)

	printNode(myid, "Newfun")
	printEdges(myid, List(xid, mid, nid))
	myid
      }

      case ToObj(x,e) => {
	val xid = output(x)
	val eid = output(e)

	printNode(myid, "ToObj")
	printEdges(myid, List(xid, eid))
	myid
      }

      case Del(x,e1,e2) => {
	val xid = output(x)
	val e1id = output(e1)
	val e2id = output(e2)

	printNode(myid, "Del")
	printEdges(myid, List(xid, e1id, e2id))
	myid
      }
      
      case Update(e1,e2,e3) => {
	val e1id = output(e1)
	val e2id = output(e2)
	val e3id = output(e3)

	printNode(myid, "Update")
	printEdges(myid, List(e1id, e2id, e3id))
	myid
      }

      case Throw(e) => {
	val eid = output(e)

	printNode(myid, "Throw")
	printEdges(myid, List(eid))
	myid
      }

      case Try(s1,x,s2,s3) => {
	val s1id = output(s1)
	val xid = output(x)
	val s2id = output(s2)
	val s3id = output(s3)

	printNode(myid,"Try")
	printEdges(myid, List(s1id,xid,s2id,s3id))
	myid
      }

      case Lbl(lbl, s) => {
	val sid = output(s)

	printNode(myid, "Label: "+lbl)
	printEdges(myid, List(sid))
	myid
      }

      case Jump(lbl, e) => {
	val eid = output(e)

	printNode(myid, "Jump: "+lbl)
	printEdges(myid, List(eid))
	myid
      }

      case For(x,e,s) => {
	val xid = output(x)
	val eid = output(e)
	val sid = output(s)

	printNode(myid, "For")
	printEdges(myid, List(xid,eid,sid))
	myid
      }

      case Merge() => {
	printNode(myid, "Merge")
	myid
      }

      case NumAST(v: Double) => {
	printNode(myid, "Double: "+v.toString)
	myid
      }

      case BoolAST(v:Boolean) => {
	printNode(myid, "Boolean: "+v.toString)
	myid
      }

      case StrAST(v:String) => {
	printNode(myid, "String: "+v)
	myid
      }

      case UndefAST() => {
	printNode(myid, "Undef")
	myid
      }

      case NullAST() => {
	printNode(myid, "Null")
	myid
      }

      case PVar(n) => {
	printNode(myid, matchVar(n))
	myid
      }

      case Scratch(n) => {
	printNode(myid, "Scratch: " + n)
	myid
      }

      case Binop(op, e1, e2) => {
	val e1id = output(e1)
	val e2id = output(e2)

	printNode(myid, "Binop: "+matchBop(op))
	printEdges(myid, List(e1id, e2id))
	myid
      }

      case Unop(op, e) => {
	val eid = output(e)

	printNode(myid, "Unop: "+matchUop(op))
	printEdges(myid, List(eid))
	myid
      }

      case Method(self,args,s) => {
	val selfid = output(self)
	val argsid = output(args)
	val sid = output(s)

	printNode(myid, "Method")
	printEdges(myid, List(selfid, argsid, sid))
	myid
      }

      case Print(e) => {
	val eid = output(e)

	printNode(myid, "Print")
	printEdges(myid, List(eid))
	myid
      }

    }
  }

    out.println("digraph AST {")
    output(a)
    out.println( "}" )
    out.close()
  }
}
