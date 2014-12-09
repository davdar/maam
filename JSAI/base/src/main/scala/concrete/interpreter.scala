// This file contains the definitions of the notJS state transition
// rules. See the notJS semantics document Section 2.3 for the
// specification.

package notjs.concrete.interpreter

import notjs.syntax._
import notjs.concrete.init._
import notjs.concrete.domains._
import notjs.concrete.helpers.Errors._
import notjs.concrete.helpers.Helpers._
import notjs.concrete.eval._
import notjs.translator._
import java.io._
import collection.mutable.{ Map ⇒ MMap }

//——————————————————————————————————————————————————————————————————————————————
// Concrete interpreter entry point

object notJS {

  object Mutable {
    // globally mutable debug flags
    var print = false
    var testing = false
    var catchExc = false
    var printid = false
    val outputMap = MMap[Int, Set[BValue]]().withDefaultValue(Set[BValue]())

    def clear {
      Mutable.print = false
      Mutable.testing = false
      Mutable.catchExc = false
      Mutable.printid = false
      Mutable.outputMap.clear()
    }
  }
  
  def runner( args:Array[String] ): MMap[Int, Set[BValue]] = {
    Mutable.clear

    val opts = args.toSet
    Mutable.print = opts("--print")
    Mutable.testing = opts("--testing") 
    Mutable.catchExc = opts("--catchexc")
    Mutable.printid = opts("--printid")

    val ast = readAST( args(0) )

    try {
      var ς = Init.initState( ast )
      while ( !ς.fin ) ς = ς.next
      if ( Mutable.printid ) {
        println(Mutable.outputMap.toList.sortWith((a, b) ⇒ a._1 < b._1).map(t ⇒ t._1 + ": " + t._2.mkString(", ")).mkString("\n"))
      }
      Mutable.outputMap
    } 
    catch {
      case _ if Mutable.catchExc ⇒ {
        if (Mutable.print)
          println("ConcreteFailedDueToException")
        Mutable.outputMap
      } 
      case e: Throwable ⇒ { 
        println("Exception occured: "+ e.getMessage() + "\n" + e.getStackTraceString)
        Mutable.outputMap
      }
    }
  }

  def main( args:Array[String] ) {
    runner(args)
  }

  def readAST( file:String ): Stmt = {
    RunTranslator.translateFileToProgram(new File(file), Mutable.print || Mutable.printid || Mutable.testing)
  }
}

//——————————————————————————————————————————————————————————————————————————————
// State: including state transition rules
//
// we optimize the handling of translator-inserted temporary variables
// ("scratch" variables) by using a separate scratchpad memory ß in
// every state that maps the scratch variables directly to BValues
// rather than using the environment and store. this is safe because
// we guarantee that scratch variables cannot cross function
// boundaries (including recursive calls).

case class State( t:Term, ρ:Env, σ:Store, ß:Scratchpad, κs:KStack ) {
  // predicate: is this a final state?
  def fin: Boolean =
    t.isInstanceOf[ValueT] && κs.top == HaltK

  // convenient shorthand for eval
  def eval( e:Exp ): BValue = 
    Eval.eval(e, ρ, σ, ß)

  // state transition rules
  def next: State = t match {
    case StmtT( s:Stmt ) ⇒ s match {
      // rule 1
      case Decl(bind, s) ⇒ 
      	val (xs, es) = bind.unzip;
      	val (σ1, as) = alloc(σ, es map (eval))
      	val ρ1 = ρ ++ (xs zip as)
      	State(s, ρ1, σ1, ß, κs)

      // special case of rule 1 for scratch variables
      case SDecl(num, s) ⇒
      	State(s, ρ, σ, Scratchpad(num), κs)

      // rule 2
      case Seq(s :: ss) ⇒ 
      	State(s, ρ, σ, ß, κs push SeqK(ss))

      // rules 3,4
      case If(e, s1, s2) ⇒ 
      	val s = if ( eval(e) == Bool.True ) s1 else s2
      	State(s, ρ, σ, ß, κs)

      // rules 5, modified to handle scratch variables specially
      case Assign(x, e) ⇒ 
      	(x, eval(e)) match {
      	  case (x:PVar, bv) ⇒ 
      	    State(bv, ρ, σ + (ρ(x) → bv), ß, κs)

      	  case (x:Scratch, bv) ⇒
      	    State(bv, ρ, σ, ß(x) = bv, κs)
      	}

      // rules 6,7
      case While(e, s) ⇒ 
      	if ( eval(e) == Bool.True ) State(s, ρ, σ, ß, κs push WhileK(e, s))
      	else State(Undef, ρ, σ, ß, κs)

      // rule 8
      case Newfun(x, m, n) ⇒
        val ρ1 = ρ filter (m.freeVars contains _)
	val (σ1, a1) = allocFun(Clo(ρ1, m), eval(n), σ)
	x match {
	  case pv:PVar ⇒ State(a1, ρ, σ1 + (ρ(pv) → a1), ß, κs)
	  case sc:Scratch ⇒ State(a1, ρ, σ1, ß(sc) = a1, κs)
	}

      // rule 9
      case New(x, e1, e2) ⇒ 
      	val (af:Address, aa:Address) = (eval(e1), eval(e2))
      	val (σ1, a1) = allocObj( af, σ )
      	val (σ2, ß1) = x match {
      	  case pv:PVar ⇒ (σ1 + (ρ(pv) → a1), ß)
      	  case sc:Scratch ⇒ (σ1, ß(sc) = a1)
      	}
      	val σ3 = setConstr( σ2, aa )
      	applyClo( af, a1, aa, x, ρ, σ3, ß1, κs )

      // rule 10
      case ToObj(x, e) ⇒
      	val (v, σ1, ß1) = toObj( eval(e), x, ρ, σ, ß )
      	State(v, ρ, σ1, ß1, κs)

      // rule 11
      case Update(e1, e2, e3) ⇒ 
      	val (v, σ1) = updateObj( eval(e1), eval(e2), eval(e3), σ )
      	State(v, ρ, σ1, ß, κs)

      // rule 12
      case Del(x, e1, e2) ⇒ 
      	val (v, σ1, ß1) = delete( eval(e1), eval(e2), x, ρ, σ, ß )
      	State(v, ρ, σ1, ß1, κs)

      // rule 13
      case Try(s1, x, s2, s3) ⇒ 
      	State(s1, ρ, σ, ß, κs push TryK(x, s2, s3))

      // rule 14
      case Throw(e) ⇒ 
      	State(EValue(eval(e)), ρ, σ, ß, κs)

      // rule 15
      case Jump(lbl, e) ⇒ 
      	State(JValue(lbl, eval(e)), ρ, σ, ß, κs)

      // rule 16
      case Lbl(lbl, s) ⇒
      	State(s, ρ, σ, ß, κs push LblK(lbl))

      // rule 17
      case Call(x, e1, e2, e3) ⇒ 
      	applyClo( eval(e1), eval(e2), eval(e3), x, ρ, σ, ß, κs )

      // rules 18,19
      case For(x, e, s) ⇒ 
      	objAllKeys( eval(e), σ ) match {
      	  case str :: strs ⇒
      	    x match {
      	      case pv:PVar ⇒ 
            		State(s, ρ, σ + (ρ(pv) → str), ß, κs push ForK(strs, x, s))
      	      
      	      case sc:Scratch ⇒
      		      State(s, ρ, σ, ß(sc) = str, κs push ForK(strs, x, s))
      	    }
	  
      	  case _ ⇒ 
      	    State(Undef, ρ, σ, ß, κs)
	     }

      case p @ Print(e) ⇒
        if ( notJS.Mutable.print )
          println(eval(e).toString)
        if ( notJS.Mutable.testing || notJS.Mutable.printid )  
          notJS.Mutable.outputMap(p.id) = notJS.Mutable.outputMap(p.id) + eval(e)
        State(Undef, ρ, σ, ß, κs)

      // merge is a noop
      case _:Merge ⇒
        State(Undef, ρ, σ, ß, κs)

      // this can only be reached by an empty Seq, which shouldn't be possible
      case _ ⇒ 
        sys.error("Inconceivable, translator produced empty sequences?")
    }

    case ValueT( bv:BValue ) ⇒ κs.top match {
      // rule 20
      case SeqK(s :: ss) ⇒
      	State(s, ρ, σ, ß, κs repl SeqK(ss))

      // rule 21
      case SeqK(_) ⇒
        State(Undef, ρ, σ, ß, κs.pop)

      // rules 22,23
      case WhileK(e, s) ⇒
        if ( eval(e) == Bool.True ) State(s, ρ, σ, ß, κs)
        else State(Undef, ρ, σ, ß, κs.pop)

      // rule 24
      case ForK(str :: strs, x, s) ⇒
      	x match {
      	  case pv:PVar ⇒ 
      	    State(s, ρ, σ + (ρ(pv) → str), ß, κs repl ForK(strs, x, s))

      	  case sc:Scratch ⇒
      	    State(s, ρ, σ, ß(sc) = str, κs repl ForK(strs, x, s))
      	}

      // rule 25
      case _:ForK ⇒
      	State(Undef, ρ, σ, ß, κs.pop)

      // rules 26,27
      case RetK(x, ρc, isctor, ß1) ⇒
	if ( isctor && !bv.isInstanceOf[Address] )
	  x match {
	    case pv:PVar ⇒ State(Eval.eval(x, ρc, σ, ß1), ρc, σ, ß1, κs.pop)
	    case sc:Scratch ⇒ State(ß1(sc), ρc, σ, ß1, κs.pop)
	  }
	else
	  x match {
            case pv:PVar ⇒ State(bv, ρc, σ + (ρc(pv) → bv), ß1, κs.pop)
            case sc:Scratch ⇒ State(bv, ρc, σ, ß1(sc) = bv, κs.pop)
	  }

      // rule 29
      case TryK(_, _, s3) ⇒
        State(s3, ρ, σ, ß, κs repl FinK(Undef))

      // rule 32
      case CatchK(s3) ⇒
      	State(s3, ρ, σ, ß, κs repl FinK(Undef))

      // rule 34
      case FinK(v) ⇒
      	v match {
      	  case _:BValue ⇒ State(bv, ρ, σ, ß, κs.pop)
      	  case _ ⇒ State(v, ρ, σ, ß, κs.pop)
      	}

      // rule 35 (also look in JValue cases)
      case LblK(_) ⇒
      	State(bv, ρ, σ, ß, κs.pop)

      // should never happen
      case HaltK ⇒
      	sys.error("trying to transition from final state")
    }

    case ValueT( ev:EValue ) ⇒ κs.top match {
      // rule 28
      case RetK(_, ρc, _, ß1) ⇒
      	State(ev, ρc, σ, ß1, κs.pop)

      // rule 31
      case TryK(x, s2, s3) ⇒
      	State(s2, ρ, σ + (ρ(x) → ev.bv), ß, κs repl CatchK(s3))

      // rule 33 (also look in JValue cases)
      case CatchK(s3) ⇒
      	State(s3, ρ, σ, ß, κs repl FinK(ev))

      // rule 37 (also look in JValue cases)
      case _ ⇒
      	val κs1 = κs dropWhile {
      	  case _:RetK | _:TryK | _:CatchK | HaltK ⇒ false
      	  case _ ⇒ true
      	}
      	State(ev, ρ, σ, ß, κs1)
    }

    case ValueT( jv:JValue ) ⇒ κs.top match {
      // rule 30
      case TryK(_, _, s3) ⇒
      	State(s3, ρ, σ, ß, κs repl FinK(jv))

      // rule 33 (also look in EValue cases)
      case CatchK(s3) ⇒
      	State(s3, ρ, σ, ß, κs repl FinK(jv))

      // rule 35 (also look in BValue cases)
      case LblK(lbl) if lbl == jv.lbl ⇒
      	State(jv.bv, ρ, σ, ß, κs.pop)

      // rules 36,37 (also look in EValue cases)
      case _ ⇒
      	val κs1 = κs dropWhile {
      	  case _:TryK | _:CatchK | HaltK ⇒ false
      	  case LblK(lbl) if lbl == jv.lbl ⇒ false
      	  case _ ⇒ true
      	}
      	State(jv, ρ, σ, ß, κs1)
    }
  }
}
