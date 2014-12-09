// This file contains the abstract syntax tree definition for
// notJS. See the notJS semantics document Section 1 for the syntax
// specification.

package notjs.syntax

//——————————————————————————————————————————————————————————————————————————————
// AST base class

sealed abstract class AST {
  // all AST nodes should have a unique identifier
  val id = AST.id(this)

  def equalsWithID(other: AST): Boolean =
    this == other && preorderIds == other.preorderIds

  def preorderIds(): List[Int] = {
    def rs(nodes: AST*): List[Int] =
      nodes.toList.flatMap(r)

    def r(node: AST): List[Int] = 
      node.id :: (node match {
        case Decl(bindings, s) =>
          bindings.toList.flatMap( { case (v, e) => rs(v, e) } ) ++ r(s)
        case SDecl(_, s) => r(s)
        case Seq(ss) => rs(ss: _*)
        case If(e, s1, s2) => rs(e, s1, s2)
        case While(e, s) => rs(e, s)
        case Assign(x, e) => rs(x, e)
        case Call(x, e1, e2, e3) => rs(x, e1, e2, e3)
        case New(x, e1, e2) => rs(x, e1, e2)
        case Newfun(x, m, n) => rs(x, m, n)
        case ToObj(x, e) => rs(x, e)
        case Del(x, e1, e2) => rs(x, e1, e2)
        case Update(e1, e2, e3) => rs(e1, e2, e3)
        case Throw(e) => r(e)
        case Try(s1, x, s2, s3) => rs(s1, x, s2, s3)
        case Lbl(_, s) => r(s)
        case Jump(_, e) => r(e)
        case For(x, e, s) => rs(x, e, s)
        case Merge() | NumAST(_) | BoolAST(_) | StrAST(_) | UndefAST() | NullAST() | PVar(_) | Scratch(_) => List()
        case Print(e) => r(e)
        case Binop(_, e1, e2) => rs(e1, e2)
        case Unop(_, e) => r(e)
        case Method(self, args, s) => rs(self, args, s)
      })

    r(this)
  }
}

object AST {
  // helper to create the unique node identifiers. we allocate
  // identifiers in steps of numClasses to enable correct abstract
  // address construction. this still gives us a few hundred million
  // identifiers; if we start analyzing programs larger than that we
  // can upgrade ids to be longs.
  //
  // remember to update numClasses if the class set changes! this
  // would be a terrible bug to catch if we forget to do so.
  //
  var genId = 0
  val numClasses = 10
  def id( node:AST ): Int = {
    // if this fails we can run into problems with overflowing integers
    assert( genId <= 210000000 )
    genId += numClasses
    genId
  }

  def reset() {
    genId = 0
  }

  // helper to compute free program variables. scratch variables are
  // never counted as free; the translator guarantees that scratch
  // variables never need to be saved in a closure. notice that we
  // never look at a method's parameters; that's because every method
  // has the same parameters (self and args) and thus those parameters
  // cannot be captured in a closure.
  def free(node:AST): Set[PVar] =
    node match {
      case Method(self, args, s) ⇒ free(s) -- Set(self, args)
      case Decl(bind, s) ⇒ 
        val (xs, es) = bind unzip;
        (free(s) -- xs.toSet) ++ (es flatMap (free(_)))
      case SDecl(_, s) ⇒ free(s)
      case Seq(ss) ⇒ 
        ss.foldLeft( Set[PVar]() )( (acc:Set[PVar], s:Stmt) ⇒ acc ++ free(s) )
      case If(e, s1, s2) ⇒ free(e) ++ free(s1) ++ free(s2)
      case While(e, s) ⇒ free(e) ++ free(s)
      case Assign(x, e) ⇒ free(e) ++ 
        (x match { case pv:PVar ⇒ Set(pv); case _ ⇒ Set() })
      case Call(x, e1, e2, e3) ⇒ free(e1) ++ free(e2) ++ free(e3) ++ 
        (x match { case pv:PVar ⇒ Set(pv); case _ ⇒ Set() })
      case New(x, e1, e2) ⇒ free(e1) ++ free(e2) ++
        (x match { case pv:PVar ⇒ Set(pv); case _ ⇒ Set() })
      case Newfun(x, m:Method, _) ⇒ m.freeVars ++ 
        (x match { case pv:PVar ⇒ Set(pv); case _ ⇒ Set() })
      case ToObj(x, e) ⇒ free(e) ++ 
        (x match { case pv:PVar ⇒ Set(pv); case _ ⇒ Set() })
      case Del(_, e1, e2) ⇒ free(e1) ++ free(e2)
      case Update(e1, e2, e3) ⇒ free(e1) ++ free(e2) ++ free(e3)
      case Throw(e) ⇒ free(e)
      case Try(s1, x, s2, s3) ⇒ free(s1) ++ free(s2) ++ free(s3) + x
      case Lbl(_, s) ⇒ free(s)
      case Jump(_, e) ⇒ free(e)
      case For(x, e, s) ⇒ free(e) ++ free(s) ++ 
        (x match { case pv:PVar ⇒ Set(pv); case _ ⇒ Set() })
      case Print(e) ⇒ free(e)
      case Binop(_, e1, e2) ⇒ free(e1) ++ free(e2)
      case Unop(_, e) ⇒ free(e)
      case pv:PVar ⇒ Set(pv)
      case _:Merge | _:NullAST | _:UndefAST | _:BoolAST | _:NumAST |
           _:StrAST | _:Scratch ⇒ Set()
    }

  // compute the set of base ids used to allocate variables/objects
  // that can escape from this method. conservatively we'll say that
  // any allocated object can escape and that any local variable
  // captured in a closure can escape.
  def escape( m:Method ): (Set[Int], Set[Int]) = {
    // the set of locally-declared variables; the translator
    // guarantees that if there's a Decl it is the first thing in the
    // function body
    val local = m.s match {
      case Decl(bind, _) ⇒ bind.unzip._1.toSet
      case _ ⇒ Set[PVar]()
    }

    // the first component of the return tuple is base ids for
    // allocated values, the second component is for allocated
    // objects. for objects we need not just the variable's base id
    // but the entire range of numClasses, to account for the fact
    // that an allocation site generates different addresses for
    // different object classes.
    def help( s:Stmt ): (Set[Int], Set[Int]) =
      s match {
	case New(x, _, _) ⇒ (Set[Int](), (x.id until (x.id+numClasses)).toSet)
	case Newfun(x, m1, _) ⇒
	  val ois = (x.id until (x.id+numClasses)).toSet
	  val vis = (local & m1.freeVars) map ( _.id ) // captured vars
	  (vis, ois)
	case ToObj(x, _) ⇒ (Set[Int](), (x.id until (x.id+numClasses)).toSet)
	case Decl(_, s) ⇒ help(s)
	case SDecl(_, s) ⇒ help(s)
	case Seq(ss) ⇒ ss.foldLeft( (Set[Int](), Set[Int]()) )(
	  (acc, s) ⇒ {
	    val vo = help(s)
	    (acc._1 ++ vo._1, acc._2 ++ vo._2)
	  })
	case If(_, s1, s2) ⇒
	  val vo1 = help(s1)
	  val vo2 = help(s2)
	  (vo1._1 ++ vo2._1, vo1._2 ++ vo2._2)
	case While(_, s) ⇒ help(s)
	case Try(s1, _, s2, s3) ⇒
	  val vo1 = help(s1)
	  val vo2 = help(s2)
	  val vo3 = help(s3)
	  (vo1._1 ++ vo2._1 ++ vo3._1, vo1._2 ++ vo2._2 ++ vo3._2)
	case Lbl(_, s) ⇒ help(s)
	case For(_, _, s) ⇒ help(s)
	case _:Assign | _:Call | _:Del | _:Update | _:Throw | _:Jump | _:Merge | _:Print ⇒ (Set[Int](), Set[Int]())
      }

    help(m.s)
  }
}

//——————————————————————————————————————————————————————————————————————————————
// Decl and Statement

// we make Decl a subclass of Stmt for convenience, though technically
// they are separate. as an optimization we separate out SDecl
// ("scratch" declarations) to declare translator-generated temporary
// variables, which the interpreters can treat specially for
// performance and precision. we include a "merge" statement as
// mentioned in the semantics document Section 3.
sealed abstract class Stmt extends AST
case class Decl(bind:List[(PVar,Exp)], s:Stmt) extends Stmt
case class SDecl(num:Int, s:Stmt) extends Stmt
case class Seq(ss:List[Stmt]) extends Stmt
case class If(e:Exp, s1:Stmt, s2:Stmt) extends Stmt
case class While(e:Exp, s:Stmt) extends Stmt
case class Assign(x:Var, e:Exp) extends Stmt
case class Call(x:Var, e1:Exp, e2:Exp, e3:Exp) extends Stmt
case class New(x:Var, e1:Exp, e2:Exp) extends Stmt
case class Newfun(x:Var, m:Method, n:NumAST) extends Stmt
case class ToObj(x:Var, e:Exp) extends Stmt
case class Del(x:Scratch, e1:Exp, e2:Exp) extends Stmt
case class Update(e1:Exp, e2:Exp, e3:Exp) extends Stmt
case class Throw(e:Exp) extends Stmt
case class Try(s1:Stmt, x:PVar, s2:Stmt, s3:Stmt) extends Stmt
case class Lbl(lbl:String, s:Stmt) extends Stmt
case class Jump(lbl:String, e:Exp) extends Stmt
case class For(x:Var, e:Exp, s:Stmt) extends Stmt
case class Merge() extends Stmt {
  // once the AST is created, we'll number the Merge statements in
  // topological order to help make the worklist algorithm faster
  var order = this.id
}

// the print statement is to aid debugging, technically it isn't part
// of the notJS language
case class Print(e: Exp) extends Stmt

//——————————————————————————————————————————————————————————————————————————————
// Expression
//
// !! OPT: it might be worthwhile to have two kinds of syntactic
//         strings, one for numbers and one for non-numbers. the
//         benefit to the abstract interpreter is that we don't need
//         to check is a string is a number or not each time we
//         abstract a concrete string.

// Num, Bool, Str, Undef, and Null are given an 'AST' suffix to
// distinguish from the semantic values of the same name. we use case
// classes instead of case objects for Undef and Null to ensure that
// the generated AST is a tree instead of a graph.
sealed abstract class Exp extends AST
case class NumAST(v:Double) extends Exp
case class BoolAST(v:Boolean) extends Exp
case class StrAST(v:String) extends Exp
case class UndefAST() extends Exp
case class NullAST() extends Exp

// variable expressions: we distinguish between scratch variables
// Scratch and program variables PVar. the translator maps variable
// names to integers to make the interpreter more efficient; it also
// provides a reverse mapping to recover the names.
sealed abstract class Var extends Exp
case class PVar(n:Int) extends Var
case class Scratch(n:Int) extends Var

case class Binop(op:Bop, e1:Exp, e2:Exp) extends Exp
case class Unop(op:Uop, e:Exp) extends Exp

//——————————————————————————————————————————————————————————————————————————————
// Methods

case class Method(self:PVar, args:PVar, s:Stmt) extends AST {
  // cache the free variables of this method for later use
  val freeVars = AST.free(this)

  // cache the base ids of addresses that can escape from this method,
  // differentiating between ids used to allocate local variables and
  // ids used to allocate objects
  val (canEscapeVar, canEscapeObj) = AST.escape(this)

  // cache the base ids of addresses that cannot escape from this
  // method; this is used by lightweight GC
  val cannotEscape:Set[Int] = s match {
    case Decl(bind, _) ⇒ 
      ((bind map (_._1.id)).toSet -- canEscapeVar) ++ Set(self.id, args.id)
    case _ ⇒ Set[Int]()
  }
}

//——————————————————————————————————————————————————————————————————————————————
// Binary and Unary operators

// binary operators
sealed abstract class Bop

// binary operators on numbers
case object ⌜+⌝ extends Bop
case object ⌜−⌝ extends Bop
case object ⌜×⌝ extends Bop
case object ⌜÷⌝ extends Bop
case object ⌜%⌝ extends Bop
case object ⌜<<⌝ extends Bop
case object ⌜>>⌝ extends Bop
case object ⌜>>>⌝ extends Bop
case object ⌜<⌝ extends Bop
case object ⌜≤⌝ extends Bop
case object ⌜&⌝ extends Bop
case object ⌜|⌝ extends Bop
case object ⌜⊻⌝ extends Bop
case object ⌜&&⌝ extends Bop
case object ⌜||⌝ extends Bop

// binary operators on strings
case object ⌜++⌝ extends Bop
case object ⌜≺⌝ extends Bop
case object ⌜≼⌝ extends Bop

// binary operator on more than one type
case object ⌜≈⌝ extends Bop
case object ⌜≡⌝ extends Bop
case object ⌜⋆⌝ extends Bop
case object InstanceOf extends Bop
case object In extends Bop

// unary operators
sealed abstract class Uop

// unary operators on numbers
case object ⌞−⌟ extends Uop
case object ⌞~⌟ extends Uop

// unary operator on booleans
case object ⌞¬⌟ extends Uop

// unary operators on more than one type
case object Typeof extends Uop
case object ToBool extends Uop
case object IsPrim extends Uop
case object ToStr extends Uop
case object ToNum extends Uop

//——————————————————————————————————————————————————————————————————————————————
// JS object classes
//

sealed abstract class JSClass
case object CObject extends JSClass
case object CFunction extends JSClass
case object CArray extends JSClass
case object CString extends JSClass
case object CBoolean extends JSClass
case object CNumber extends JSClass
case object CDate extends JSClass
case object CError extends JSClass
case object CRegexp extends JSClass
case object CArguments extends JSClass

// these are the special classes that only exist in the init state
case object CObject_Obj extends JSClass
case object CObject_prototype_Obj extends JSClass
case object CArray_Obj extends JSClass
case object CArray_prototype_Obj extends JSClass
case object CFunction_Obj extends JSClass
case object CFunction_prototype_Obj extends JSClass
case object CMath_Obj extends JSClass
case object CNumber_Obj extends JSClass
case object CNumber_prototype_Obj extends JSClass
case object CString_Obj extends JSClass
case object CString_prototype_Obj extends JSClass
// TODO: window, RegExp, Error, ...

//——————————————————————————————————————————————————————————————————————————————
// Topological ordering of Merge statements
//
// the ordering is only valid intraprocedurally; at this point we
// don't know the proper ordering between methods.

object Topo {
  import scala.collection.mutable.HashSet

  def order( s:Stmt ): Unit = {
    var ordnum = 0

    def number( node:AST ): Unit =
      node match {
      	case m:Merge ⇒
      	  m.order = ordnum
      	  ordnum += 1
      	case Decl(_, s) ⇒ number(s)
      	case SDecl(_, s) ⇒ number(s)
      	case Seq(ss) ⇒ ss.foreach( number(_) )
      	case If(_, s1, s2) ⇒ number(s1); number(s2)
      	case While(_, s) ⇒ number(s)
      	case Try(s1, _, s2, s3) ⇒ number(s1); number(s2); number(s3)
      	case Lbl(_, s) ⇒ number(s)
      	case For(_, _, s) ⇒ number(s)
      	case Newfun(_, Method(_, _, s), _) ⇒ number(s)
      	case _ ⇒ ()
      }

    number(s)
  }

}
