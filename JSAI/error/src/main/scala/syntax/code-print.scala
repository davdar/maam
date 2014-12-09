package notjs.syntax
import notjs.translator.RunTranslator
import notjs.translator.PVarMapper
import java.io._

object CodePrint {
  var withColors = false

  def main(args: Array[String]) {
    assert(args.length >= 2, "Needs an input notJS file and an output dot filename")
    val ast = RunTranslator.translateFileToProgram(new File(args(0)), args.toSet("--debug"))
    val mapping = PVarMapper.getMapping
    writeText(ast, mapping, args(1))
  }

  def writeText(a: AST, reverseMapping: Map[Int, String], file: String) {
    val out = new PrintWriter(new BufferedWriter(new FileWriter(file)))
  
    def strId(node: AST) = node.id.toString
    
    def getStr(n: Int) = reverseMapping(n)
  
    def outputBinding(binding: Tuple2[PVar,Exp]): String = {
      expToStr(binding._1) + " = " + expToStr(binding._2)
    }
  
    def matchBop(b: Bop): String = (if (withColors) "\033[93m" else "") + (b match {
      case ⌜+⌝ => "⌜+⌝"
      case ⌜−⌝ => "⌜−⌝"
      case ⌜×⌝ => "⌜×⌝"
      case ⌜÷⌝ => "⌜÷⌝"
      case ⌜%⌝ => "⌜%⌝"
      case ⌜<<⌝ => "⌜<<⌝"
      case ⌜>>⌝ => "⌜>>⌝"
      case ⌜>>>⌝ => "⌜>>>⌝"
      case ⌜<⌝ => "⌜<⌝"
      case ⌜≤⌝ => "⌜≤⌝"
      case ⌜&⌝ => "⌜&⌝"
      case ⌜|⌝ => "⌜|⌝"
      case ⌜⊻⌝ => "⌜⊻⌝"
      case ⌜&&⌝ => "⌜&&⌝"
      case ⌜||⌝ => "⌜||⌝"
      case ⌜++⌝ => "⌜++⌝"
      case ⌜≺⌝ => "⌜≺⌝"
      case ⌜≼⌝ => "⌜≼⌝"
      case ⌜≈⌝ => "⌜≈⌝"
      case ⌜≡⌝ => "⌜≡⌝"
      case ⌜⋆⌝ => "⌜⋆⌝"
      case InstanceOf => "instanceof"
      case In => "in"
    }) + (if (withColors) "\033[0m" else "")
    
    def matchUop(u: Uop): String = (if (withColors) "\033[93m" else "") + (u match {
      case ⌞−⌟ => "⌞−⌟"
      case ⌞~⌟ => "⌞~⌟"
      case ⌞¬⌟ => "⌞¬⌟"
      case Typeof => "typeof"
      case ToBool => "tobool"
      case IsPrim => "isprim"
      case ToStr => "tostr"
      case ToNum => "tonum"
    }) + (if (withColors) "\033[0m" else "")
  
    def printNode(depth: Int, id: String, label: String) {
      val prefix = "  "*depth
      val fpart = prefix + label
      //val suffix = if(fpart.length<70) " "*(70-fpart.length) else ""
      out.println(fpart /*+ suffix + "ID: " + id*/)
    }

    // Exps should always be output inline
    def expToStr(node: Exp): String = node match {
      case NumAST(v) => v.toString
      case BoolAST(v) => v.toString 
      case StrAST(v) => "\"" + v + "\""
      case UndefAST() => "undef"
      case NullAST() => "null"
      case PVar(n) => getStr(n)
      case Scratch(n) => "scratch_"+n.toString
      case Binop(op, e1, e2) => expToStr(e1) + " " + matchBop(op) + " " + expToStr(e2)
      case Unop(op, e) => matchUop(op) + " " + expToStr(e)
    }
    
    def output(depth: Int)(node: AST): String = {
      val myid = strId(node)
  
      node match {
        case Decl(bind,s) => {
          val bindingIDs = bind map outputBinding

          printNode(depth, myid, "decl "+bindingIDs.mkString(", ")+" in")
  
          val sid = output(depth+1)(s)
  
          myid
        }

      	case SDecl(bound, s) => {
      	  printNode(depth, myid, "scratch ("+bound.toString+") in")
      	  output(depth + 1)(s)
      	  myid
      	}
        
        case Seq(ss) => {
          val ids = ss map output(depth+1)
  
          myid
        }
    
        case If(e,s1,s2) => {
          printNode(depth, myid, "if "+expToStr(e))
  
          val s1id = output(depth+1)(s1)

          printNode(depth, myid, "else")
          val s2id = output(depth+1)(s2)
  
          myid
        }
    
        case While(e, s) => {
          printNode(depth, myid, "while "+expToStr(e))
  
          val sid = output(depth+1)(s)
  
          myid
        }
    
        case Assign(x, e) => {
          printNode(depth, myid, expToStr(x)+" = "+expToStr(e))
  
          myid
        }
    
        case Call(x,e1,e2,e3) => {
          printNode(depth, myid, expToStr(x)+" = "+ expToStr(e1) + "(" + expToStr(e2) + ", "+ expToStr(e3)+")")
  
          myid
        }
    
        case New(x,e1,e2) => {
          printNode(depth, myid, expToStr(x)+ " = new " + expToStr(e1) + "(" + expToStr(e2) + ")")
  
          myid
        }
    
        case Newfun(x,m,n) => {
          printNode(depth, myid, expToStr(x) + " = newfun (" + expToStr(n) + ")")
  
          val mid = output(depth+1)(m)
  
          myid
        }
    
        case ToObj(x,e) => {
          printNode(depth, myid, expToStr(x) + " = toObj " + expToStr(e))
  
          myid
        }
    
        case Del(x,e1,e2) => {
          printNode(depth, myid, expToStr(x) + " = delete ("+expToStr(e1)+")." + "("+ expToStr(e2) + ")")
  
          myid
        }
        
        case Update(e1,e2,e3) => {
          printNode(depth, myid, "("+ expToStr(e1) + ").("+ expToStr(e2) + ") = " + expToStr(e3))
  
          myid
        }
    
        case Throw(e) => {
          printNode(depth, myid, "throw "+expToStr(e))
  
          myid
        }
    
        case Try(s1,x,s2,s3) => {
          printNode(depth, myid,"try")
  
          val s1id = output(depth+1)(s1)
          printNode(depth, myid, "catch "+expToStr(x))
          val s2id = output(depth+1)(s2)
          printNode(depth,myid, "finally")
          val s3id = output(depth+1)(s3)
  
          myid
        }
    
        case Lbl(lbl, s) => {
          printNode(depth, myid, lbl+": ")
  
          val sid = output(depth+1)(s)
  
          myid
        }
    
        case Jump(lbl, e) => {
          printNode(depth, myid, "jmp "+lbl+ " " + expToStr(e))
  
          myid
        }
    
        case For(x,e,s) => {
          printNode(depth, myid, "for "+expToStr(x)+" "+expToStr(e))

          val sid = output(depth+1)(s)
  
          myid
        }
    
        case Merge() => {
          printNode(depth, myid, "merge")
          myid
        }
    
        case Method(self,args,s) => {
          printNode(depth, myid, "("+expToStr(self)+", "+expToStr(args)+") =>")
  
          val sid = output(depth+1)(s)
  
          myid
        }
    
        case Print(e) => {
          printNode(depth, myid, "print "+expToStr(e))
  
          myid
        }

        case _ => { println("Tried to print non-method exp in statement context"); "" }
  
      }
    }
  
    //out.println("digraph AST {")
    output(0)(a)
    //out.println( "}" )
    out.close()
  }
}
