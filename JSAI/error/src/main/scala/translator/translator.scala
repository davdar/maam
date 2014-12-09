package notjs.translator

import notjs.syntax.{Seq => SyntaxSeq, _}
import notjs.translator.jsast._
import scala.collection.mutable.{HashMap => MMap}
import scala.annotation.tailrec

object PVarMapper {
  private val numToName = new MMap[Int, String]()
  private val nameToNum = new MMap[String, Int]()
  private var counter: Int = 0

  val WINDOW_NAME = "window"
  val ARGUMENTS_NAME = "arguments"

  // at the end of the analysis, we will clone the whole AST anyway,
  // so it's of no use to try to prevent node duplication
  val window = newMangledVar(WINDOW_NAME) // reserve PVar(0) for window
  assert(window.n == 0)
  val windowName = getName(window)
  val unmangledWindow = getPVar(WINDOW_NAME)

  val global = window
  val dummy = newMangledVar("dummy") // reserve PVar(1) for a dummy variable

  val arrayVar = newMangledVar("arrayVar")
  val functionVar = newMangledVar("functionVar")
  val stringVar = newMangledVar("stringVar")
  val regexpVar = newMangledVar("regexpVar")
  val booleanVar = newMangledVar("booleanVar")
  val numberVar = newMangledVar("numberVar")
  val dateVar = newMangledVar("dateVar")
  val errorVar = newMangledVar("errorVar")
  val argumentsVar = newMangledVar("argumentsVar")
  val objectVar = newMangledVar("objectVar")
  val dummyAddressVar = newMangledVar("dummyAddressVar")

  val selfVar = newMangledVar("self")
  val selfName = getName(selfVar)

  val counterReset = counter
  val astCounterReset = AST.genId
  val numToNameReset = numToName.toMap
  val nameToNumReset = nameToNum.toMap

  // a marker that we are wrapping around what was originally a JS sequence
  val INDICATE_JS_SEQUENCE = List((PVarMapper.dummy, NullAST()))

  val noOpStatement = Assign(PVarMapper.dummy, UndefAST())

  // this is needed to get around the lazy instantiation of Scala classes
  // if AST nodes start getting created before PVarMapper is instantiated, then
  // it can result in nondeterministic node ids
  def forceInitialization() {}

  def getMapping(): Map[Int,String] =
    numToName.toMap

  def windowAccess(str: String): Exp =
    Binop(⌜⋆⌝, window, StrAST(str))

  def reset() {
    numToName.clear()
    numToName ++= numToNameReset
    nameToNum.clear()
    nameToNum ++= nameToNumReset
    counter = counterReset
    AST.genId = astCounterReset
  }

  def getName(i: Int): String =
    numToName(i)

  def getName(v: PVar): String =
    getName(v.n)

  def getNum(name: String): Int =
    nameToNum(name)

  def getPVar(name: String): PVar = 
    if (nameToNum.contains(name))
      PVar(nameToNum(name))
    else
      newVar(name)
  
  def getVar(v: JSVar): Var =
    v match {
      case JSPVar(name) => getPVar(name)
      case JSScratch(id) => Scratch(id)
    }

  private def newVar(name: String): PVar = {
    val retvalCount = counter
    counter += 1
    numToName.put(retvalCount, name)
    nameToNum.put(name, retvalCount)
    PVar(retvalCount)
  }

  def freshPVar(): PVar =
    newMangledVar("tempPVar")

  def newMangledVar(name: String): PVar =
    getPVar("`" + name + "`" + counter)
}

object Translator {
  type TranslationRetval = (Stmt, Exp, Set[PVar])

  PVarMapper.forceInitialization()

  val TYPE_ERROR = "TypeError"
  val OBJECT_TYPE = "object"
  val STRING_TYPE = "string"
  val LENGTH_FIELD = "length"
  val VALUE_OF = "valueOf"
  val TO_STRING = "toString"
  val RETURN_LABEL = ":RETURN:"
  val BREAK_LABEL = ":BREAK:"
  val CONTINUE_LABEL = ":CONTINUE:"					       
  val FUNCTION_TYPE = "function"


  def apply(j: JSAST): Stmt =
    new Translator(j).translate()

  // given two Seqs of equal length like so:
  // Seq(1, 2, 3)
  // Seq(4, 5, 6)
  // ...
  // this returns a new Seq like so: Seq(1, 4, 2, 5, 3, 6)
  def interleave[T](s1: Seq[T], s2: Seq[T]): Seq[T] = {
    @tailrec
    def recurse(s1: List[T], s2: List[T], accum: List[T]): List[T] =
      (s1, s2) match {
        case (item1 :: rest1, item2 :: rest2) =>
          recurse(rest1, rest2, item2 :: item1 :: accum)
        case (Nil, Nil) => accum.reverse
        case (lst1, Nil) => accum.reverse ++ lst1
        case (Nil, lst2) => accum.reverse ++ lst2
      }
    recurse(s1.toList, s2.toList, List()).toSeq
  }

  // begin wrappers that insert merge nodes
  def makeIf(e: Exp, s1: Stmt, s2: Stmt): Stmt =
    ConstantFolding(e) match {
      case BoolAST(true) => s1
      case BoolAST(false) => s2
      case ep =>
        asSeq(If(ep, s1, s2), Merge())
    }

  def makeWhile(e: Exp, s: Stmt): Stmt =
    asSeq(While(e, asSeq(Merge(), s)), Merge())

  def makeFor(x: Var, e: Exp, s: Stmt): Stmt =
    asSeq(For(x, e, asSeq(Merge(), s)), Merge())

  def makeLbl(lbl: String, s: Stmt): Stmt =
    asSeq(Lbl(lbl, s), Merge())

  def makeCall(x: Var, e1: Exp, e2: Exp, e3: Exp): Stmt =
    asSeq(Call(x, e1, e2, e3), Merge())
  
  def makeNew(x: Var, e1: Exp, e2: Exp): Stmt =
    asSeq(New(x, e1, e2), Merge())

  def makeTry(s1: Stmt, x: PVar, s2: Stmt, s3: Stmt): Stmt =
    Try(s1, x, asSeq(Merge(), s2), asSeq(Merge(), s3))
  // end wrappers that insert merge nodes

  def noOpStatement(e: Exp): TranslationRetval =
    (PVarMapper.noOpStatement, e, Set())

  def noOpRetval(): TranslationRetval = noOpStatement(UndefAST())

  def asSeq(as: Stmt*): Stmt =
    SyntaxSeq(as.toList)
}
import Translator._

// performs the JS -> notJS pass
class Translator(val fromAst: JSAST) {
  import PVarMapper.{windowName, ARGUMENTS_NAME}
  private var scratchCounter = MaxScratchId.maxId(fromAst).map(_ + 1).getOrElse(0)
  val throwTypeError = Throw(StrAST(TYPE_ERROR))

  def freshScratch(): Scratch = {
    val retval = Scratch(scratchCounter)
    scratchCounter += 1
    retval
  }

  def freshVar(): PVar = 
    PVarMapper.freshPVar

  // target will hold the result of the call afterward
  def call(target: Var, toCall: Exp, self: Exp, args: Seq[Exp]): TranslationRetval = {
    val (argsStmt, argsExp, argsys) = makeArguments(args)
    (asSeq(argsStmt, makeCall(target, toCall, self, argsExp)), UndefAST(), argsys)
  }
  
  def callMethodByName(target: Var, obj: Exp, name: String, args: Seq[Exp]): TranslationRetval =
    call(target, Binop(⌜⋆⌝, obj, StrAST(name)), obj, args)

  def callValueOf(target: Var, obj: Exp): TranslationRetval =
    callMethodByName(target, obj, VALUE_OF, Seq(BoolAST(true)))

  def callToString(target: Var, obj: Exp): TranslationRetval =
    callMethodByName(target, obj, TO_STRING, Seq())

  def callNumber(target: Var, arg: Exp): TranslationRetval = 
    call(target, PVarMapper.numberVar, PVarMapper.global, Seq(arg))

  def makeArguments(args: Seq[Exp]): TranslationRetval = {
    val y = freshScratch
    (asSeq(makeNew(y, PVarMapper.argumentsVar, PVarMapper.dummyAddressVar),
	   asSeq(
	     args.zip(0 until args.size).map(
	       { case (arg, num) => Update(y, StrAST(num.toString), arg) }): _*),
	   Update(y, StrAST(LENGTH_FIELD), NumAST(args.size))),
     y, Set())
  }

  def flattenVars(vars: Iterable[Set[PVar]]): Set[PVar] =
    vars.foldLeft(Set[PVar]())(_ ++ _)

  // given the expressions for an object and a field, it returns
  // the statement to execute for them, along with the implicitly converted
  // object and field expressions
  def accessSetup(obj: Exp, field: Exp): (Stmt, Exp, Exp, Set[PVar]) = {
    val (objS, objE, objys) = toObj(obj)
    val (stringS, stringE, stringys) = toString(field)
    (asSeq(objS, stringS), objE, stringE, objys ++ stringys)
  }

  def toObj(e: Exp): TranslationRetval = {
    import PVarMapper.window
    e match {
      case `window` => noOpStatement(e)
      case _ => {
        val y = freshScratch
        (ToObj(y, e), y, Set())
      }
    }
  }

  def staticIsPrim(e: Exp): Option[Boolean] =
    TypeInferencer(e).isPrim

  def isPrimToString(e: Exp): Exp =
    TypeInferencer(e) match {
      case StrT => e
      case _ => Unop(ToStr, e)
    }

  def isPrimToNumber(e: Exp): Exp =
    TypeInferencer(e) match {
      case NumT => e
      case _ => Unop(ToNum, e)
    }

  def toBool(e: Exp): Exp =
    TypeInferencer(e) match {
      case BoolT => e
      case _ => Unop(ToBool, e)
    }

  // Converts e to some type.  ifPrim will perform the conversion if it's a primitive
  // already.  ifNotPrim will do the conversion if not.
  def toSomething(e: Exp, ifPrim: Exp => Exp, ifNotPrim: (Var, Exp) => TranslationRetval): TranslationRetval = {
    def notPrim(): (Stmt, Scratch, Set[PVar]) = {
      val y = freshScratch
      val (s, _, vars) = ifNotPrim(y, e)
      (s, y, vars)
    }

    staticIsPrim(e) match {
      case Some(true) =>
        noOpStatement(ifPrim(e))
      case Some(false) =>
        notPrim
      case None => {
        val (s, y, ys) = notPrim
        (makeIf(Unop(IsPrim, e),
                Assign(y, ifPrim(e)),
                s),
         y, ys)
      }
    }
  } // toNumber
    
  def toNumber(e: Exp): TranslationRetval =
    toSomething(e, isPrimToNumber, callNumber)

  def toString(e: Exp): TranslationRetval =
    toSomething(e, isPrimToString, callToString)

  def valueOf(e: Exp): TranslationRetval =
    toSomething(e, (e: Exp) => e, callValueOf)

  def unzip4[A, B, C, D](items: Seq[(A, B, C, D)]): (Seq[A], Seq[B], Seq[C], Seq[D]) =
    items.foldRight((List[A](), List[B](), List[C](), List[D]()))((cur, res) => 
      (cur._1 :: res._1, cur._2 :: res._2,
       cur._3 :: res._3, cur._4 :: res._4))

  def JSBopToBop(j: JSBop): Bop =
    j match {
      case JSSub => ⌜−⌝
      case JSMul => ⌜×⌝
      case JSDiv => ⌜÷⌝
      case JSMod => ⌜%⌝
      case JSShiftLeft => ⌜<<⌝
      case JSShiftRight => ⌜>>⌝
      case JSUShiftRight => ⌜>>>⌝
      case JSBitAnd => ⌜&⌝
      case JSBitOr => ⌜|⌝
      case JSBitXOr => ⌜⊻⌝
      case _ => throw BadTransformation("Found unrecognized JSBop: " + j)
    }

  def optionLabel(label: Option[JSLabel], orElse: String): String =
    label.map(_.name).getOrElse(orElse)

  // while there is duplication between prefixVarHelper and postfixVarHelper,
  // they are so short that any attempt to remove duplication will add bloat and
  // complication
  def prefixVarHelper(xJS: JSVar, inc: Double): TranslationRetval = {
    val x = PVarMapper.getVar(xJS)
    val (numS, numE, ys) = toNumber(x)
    (asSeq(numS, Assign(x, Binop(⌜+⌝, numE, NumAST(inc)))),
     x, ys)
  }

  def postfixVarHelper(xJS: JSVar, inc: Double): TranslationRetval = {
    val x = PVarMapper.getVar(xJS)
    val (numS, numE, ys) = toNumber(x)
    val y = freshScratch
    (asSeq(numS, Assign(y, numE), Assign(x, Binop(⌜+⌝, y, NumAST(inc)))),
     y, ys)
  }

  // -shouldReturn is a function that takes an expression that represents the value as a number.
  //  It returns what should be returned from the pre/post operator as a whole.
  // -updateTo is a function that takes the temporary variable holding the result of
  //  assignRhs.  It returns what this object field should be updated to.
  def prepostAccessHelper(e1: JSExp, e2: JSExp, shouldReturn: Exp => Exp, updateTo: Scratch => Exp): TranslationRetval = {
    val (e1s, e1e, e1y) = translate(e1)
    val (e2s, e2e, e2y) = translate(e2)
    val (s, obj, field, accessys) = accessSetup(e1e, e2e)
    val (numS, numE, numY) = toNumber(Binop(⌜⋆⌝, obj, field))
    val y = freshScratch
    (asSeq(e1s,
	   e2s,
	   s,
	   numS,
	   Assign(y, shouldReturn(numE)),
	   Update(obj, field, updateTo(y))),
     y, e1y ++ e2y ++ numY ++ accessys)
  }

  def prefixAccessHelper(e1: JSExp, e2: JSExp, inc: Double): TranslationRetval =
    prepostAccessHelper(e1, e2,
                        (asNum: Exp) => Binop(⌜+⌝, asNum, NumAST(inc)),
                        (y: Scratch) => y)

  def postfixAccessHelper(e1: JSExp, e2: JSExp, inc: Double): TranslationRetval =
    prepostAccessHelper(e1, e2,
                        (numE: Exp) => numE,
                        (y: Scratch) => Binop(⌜+⌝, y, NumAST(inc)))

  def preambleBindings(): List[(PVar, Exp)] = {
    import PVarMapper.windowAccess
    List((PVarMapper.dummy, UndefAST()),
	 (PVarMapper.arrayVar, windowAccess("Array")),
	 (PVarMapper.functionVar, windowAccess("Function")),
	 (PVarMapper.stringVar, windowAccess("String")),
	 (PVarMapper.regexpVar, windowAccess("RegExp")),
	 (PVarMapper.booleanVar, windowAccess("Boolean")),
	 (PVarMapper.numberVar, windowAccess("Number")),
	 (PVarMapper.dateVar, windowAccess("Date")),
	 (PVarMapper.errorVar, windowAccess("Error")),
	 (PVarMapper.argumentsVar, windowAccess("Arguments")),
	 (PVarMapper.objectVar, windowAccess("Object")),
	 (PVarMapper.dummyAddressVar, windowAccess("dummyAddress")),
         (PVarMapper.unmangledWindow, PVarMapper.window))
  }

  // the guards are given boolean conversion
  def whileHelper(beforeLoop: Stmt, initialGuard: Exp, normalGuard: Exp, body: Stmt, afterBody: Stmt): TranslationRetval = {
    // Scratch variables are ok here, only because it only needs to survive
    // the portion in between the end of the loop and the check of the guard again.
    // The JS statements in between 
    val y = freshScratch
    (makeLbl(BREAK_LABEL,
             asSeq(beforeLoop,
                   Assign(y, toBool(initialGuard)),
                   makeWhile(y,
                             asSeq(makeLbl(CONTINUE_LABEL, body),
                                   afterBody,
                                   Assign(y, toBool(normalGuard)))))),
     UndefAST(), Set())
  }

  // statement that starts any NotJS program
  def preamble(s: Stmt): Stmt = {
    def makeRetval(extraBindings: List[(PVar, Exp)], rest: Stmt): Stmt = {
      Decl(extraBindings ++ preambleBindings,
	   asSeq(Update(PVarMapper.window, StrAST("dummyAddress"), UndefAST()),
		 Update(PVarMapper.window, StrAST("Arguments"), UndefAST()),
		 rest))
    }

    s match {
      case Decl(origBindings, rest) =>
	makeRetval(origBindings, rest)
      case _ => 
	makeRetval(List(), s)
    }
  }

  def translate(): Stmt =
    preamble(translate(fromAst)._1)

  def translate(j: JSAST): TranslationRetval = 
    j match {
      case JSToplevelDecl(vars, rest) => {
        val oldBindings = vars.toList.map(x => (PVarMapper.getPVar(x.name), UndefAST()))
        val (newRest, _, restY) = translate(rest)
        val newBindings = restY.toList.map(x => (x, UndefAST()))
        (Decl(
          oldBindings ++ newBindings,
          newRest),
         UndefAST(), Set())
      }

      case JSNum(n) => 
	noOpStatement(NumAST(n))

      case JSBool(b) => 
	noOpStatement(BoolAST(b))

      case JSStr(s) => 
	noOpStatement(StrAST(s))

      case JSUndef() =>
	noOpStatement(UndefAST())

      case JSNull() => 
	noOpStatement(NullAST())

      case JSEmpty() =>
	throw BadTransformation("Found empty expression")

      case v: JSVar =>
        noOpStatement(PVarMapper.getVar(v))

      case JSSimpleAssign(v: JSVar, rhs) => {
	val (s, e, ys) = translate(rhs)
	(asSeq(s, Assign(PVarMapper.getVar(v), e)),
         e, ys)
      }

      case JSCompoundAssign(_, _, _) => 
	throw BadTransformation("Found compound assignment")

      // optimized for window
      case JSSimpleUpdate(JSAccess(JSPVar(`windowName`), JSStr(string)), rhs) => {
        val (rhss, rhse, rhsys) = translate(rhs)
        (asSeq(rhss,
               Update(PVarMapper.window, StrAST(string), rhse)),
         rhse, rhsys)
      }

      case JSSimpleUpdate(JSAccess(e1, e2), e3) => {
        val (e1s, e1e, e1ys) = translate(e1)
        val (e2s, e2e, e2ys) = translate(e2)
        val (e3s, e3e, e3ys) = translate(e3)
        val (accessS, obj, field, fieldys) = accessSetup(e1e, e2e)
        (asSeq(e3s, e1s, e2s, accessS, Update(obj, field, e3e)),
         e3e, e1ys ++ e2ys ++ e3ys ++ fieldys)
      }

      case JSCompoundUpdate(_, _, _) =>
	throw BadTransformation("Found compound update")

      case JSRegexp(JSStr(string), flags) => {
        val flagArg = 
          if (flags.isEmpty)
            List[StrAST]()
          else
            List(StrAST(flags.map(_.flag).mkString))
        val (sargs, eargs, eys) = makeArguments(StrAST(string) :: flagArg)
        val y = freshScratch
        (asSeq(sargs, makeNew(y, PVarMapper.regexpVar, eargs)),
         y, eys)
      }

      case JSTernary(e1, e2, e3) => {
        val (e1s, e1e, e1ys) = translate(e1)
        val (e2s, e2e, e2ys) = translate(e2)
        val (e3s, e3e, e3ys) = translate(e3)
        val yRetval = freshScratch
        (asSeq(e1s, makeIf(toBool(e1e),
			   asSeq(e2s, Assign(yRetval, e2e)),
			   asSeq(e3s, Assign(yRetval, e3e)))),
         yRetval, e1ys ++ e2ys ++ e3ys)
      }

      // optimized access cases
      case JSAccess(JSPVar(`windowName`), JSStr(string)) =>
        noOpStatement(Binop(⌜⋆⌝, PVarMapper.window, StrAST(string)))

      case JSAccess(e1, e2) => {
        val (e1s, e1e, e1ys) = translate(e1)
	val (e2s, e2e, e2ys) = translate(e2)
	val (accessS, obj, field, accessys) = accessSetup(e1e, e2e)
        (asSeq(e1s, e2s, accessS),
         Binop(⌜⋆⌝, obj, field),
         e1ys ++ e2ys ++ accessys)
      }

      case JSDebug(e) => {
        val (es, ee, eys) = translate(e)
        (asSeq(es, Print(ee)), UndefAST(), eys)
      }

      case JSNew(e1, e2s) => {
	val (sfp, efp, e1ys) = translate(e1)
	val (sip, eip, eiys) = e2s.map(translate).unzip3
	val pred = asSeq(sfp, asSeq(sip: _*))
        val ys = e1ys ++ flattenVars(eiys)

        staticIsPrim(efp) match {
          case Some(true) => 
            (asSeq(pred, throwTypeError), UndefAST(), ys)
          case Some(false) => {
	    val (argsStmt, argsExp, argsys) = makeArguments(eip)
	    val y = freshScratch
            (asSeq(pred,
                   argsStmt,
                   makeNew(y, efp, argsExp)),
             y, ys ++ argsys)
          }
          case None => {
	    val (argsStmt, argsExp, argsys) = makeArguments(eip)
	    val y = freshScratch
	    (asSeq(pred,
                   makeIf(Unop(IsPrim, efp),
                          throwTypeError,
	                  asSeq(argsStmt,
                                makeNew(y, efp, argsExp)))),
             y, ys ++ argsys)
          }
        }
      }

      // method call
      case JSCall(JSAccess(e1, e2), e3s) => {
	val (objS, objE, objys) = translate(e1)
	val (fieldS, fieldE, fieldys) = translate(e2)
	val (argsSs, argsEs, argsys) = e3s.map(translate).unzip3
	val (accessS, obj, field, accessys) = accessSetup(objE, fieldE)
	val y = freshScratch
	val (callStmt, _, callys) = call(y, Binop(⌜⋆⌝, obj, field), obj, argsEs)
	(asSeq(objS,
	       fieldS,
	       asSeq(argsSs: _*),
	       accessS,
	       callStmt),
         y, objys ++ fieldys ++ flattenVars(argsys) ++ callys ++ accessys)
      }

      // function call
      case JSCall(e1, e2s) => {
	val (e1s, e1e, e1ys) = translate(e1)
	val (e2ss, e2es, e2ys) = e2s.map(translate).unzip3
	val y = freshScratch
	val (callStmt, _, callys) = call(y, e1e, PVarMapper.global, e2es)
	(asSeq(e1s,
	       asSeq(e2ss: _*),
	       callStmt),
         y, e1ys ++ flattenVars(e2ys) ++ callys)
      }

      case JSFunctionExp(_, params, JSSeq(JSDecl(bindings):: body)) => {
        if (params.toSet.size != params.size) {
          throw BadTransformation(
            "Function formal parameters must all have unique identifiers")
        }
	val (bodyS, _, bodyys) = body.map(s => translate(s)).unzip3
	val args = PVarMapper.getPVar(ARGUMENTS_NAME)
	val declParams = params.zip(0 until params.size).toList.map(
	  { case (JSPVar(name), num) => 
	    (PVarMapper.getPVar(name), Binop(⌜⋆⌝, args, StrAST(num.toString))) })
	val declLocal = bindings.map(
	  { case (JSPVar(name), e) => {
	      val rhs = 
		e match {
		  case Some(JSUndef()) => UndefAST()
		  case Some(v: JSVar) => PVarMapper.getVar(v)
		  case a => throw BadTransformation("Invalid expression: " + a)
		}
	      (PVarMapper.getPVar(name), rhs)
	  } } )
	val (protoArgsS, protoArgsE, protoArgsys) = makeArguments(Seq())
        val tempBindings = flattenVars(bodyys).toList.map(y => (y -> UndefAST()))
	val decl = Decl(declParams ++ declLocal ++ tempBindings,
			Lbl(RETURN_LABEL, asSeq(Merge(), asSeq(bodyS: _*)))) // Lbl so we don't overwrite the return value
	val method = Method(PVarMapper.selfVar, args, decl)
	val yProto = freshScratch
	val yRetval = freshScratch
	(asSeq(Newfun(yRetval, method, NumAST(params.size)),
	       protoArgsS,
	       makeNew(yProto, PVarMapper.objectVar, protoArgsE),
	       Update(yRetval, StrAST("prototype"), yProto)),
         yRetval, protoArgsys)
      }

      case f: JSFunctionExp =>
	throw BadTransformation(
	  "Found a JSFunctionExp that didn't start with a Decl: " + f)

      case JSBinop(e1, op, e2) => {
	val (e1s, e1e, e1ys) = translate(e1)
	val (e2s, e2e, e2ys) = translate(e2)

	def withStatements(t: TranslationRetval): TranslationRetval =
	  (asSeq(e1s, e2s, t._1), t._2, e1ys ++ e2ys ++ t._3)

	def withStatementsExp(e: Exp): TranslationRetval =
	  (asSeq(e1s, e2s), e, e1ys ++ e2ys)

	// holds commonality between < and <=
	// swap is a hacky way of doing > and >=
	def lessThanCore(stringCompare: Bop,
			 numberCompare: Bop,
			 swap: Boolean = false): TranslationRetval = {
	  val (left, right) = if (!swap) (e1e, e2e) else (e2e, e1e)
	  val yRetval = freshScratch
          val (leftNumS, leftNumE, leftys) = toNumber(left)
          val (rightNumS, rightNumE, rightys) = toNumber(right)

	  withStatements(
            (makeIf(Binop(⌜&&⌝,
			  Binop(⌜≡⌝, Unop(Typeof, left), StrAST(STRING_TYPE)),
			  Binop(⌜≡⌝, Unop(Typeof, right), StrAST(STRING_TYPE))),
		    Assign(yRetval, Binop(stringCompare, left, right)),
                    asSeq(leftNumS,
                          rightNumS,
                          Assign(yRetval,
                                 Binop(numberCompare, leftNumE, rightNumE)))),
             yRetval, leftys ++ rightys))
	}

	// if compare equals toBool(e1), then do the second part
	def logicalHelper(compare: Exp): TranslationRetval = {
	  val yRetval = freshScratch
	  (asSeq(e1s,
		 makeIf(Binop(⌜≡⌝, toBool(e1e), compare),
			asSeq(e2s, Assign(yRetval, e2e)),
			Assign(yRetval, e1e))),
           yRetval, e1ys ++ e2ys)
	}
			     
	op match {
	  case JSSub | JSDiv | JSMul | JSMod | JSShiftLeft | JSShiftRight | JSUShiftRight | JSBitAnd | JSBitOr | JSBitXOr => {
	    val (leftS, leftE, leftys) = toNumber(e1e)
	    val (rightS, rightE, rightys) = toNumber(e2e)
            withStatements(
              (asSeq(leftS, rightS),
	       Binop(JSBopToBop(op), leftE, rightE), leftys ++ rightys))
          }

	  case JSAdd => {
            val yRetval = freshScratch

            // 1: If it's a primitive, do nothing.  Else, call valueOf on it.
            // 2: If the result of valueOf is a primitive, do nothing.  Else,
            //    try to convert it to a string.
            // 3: If the result of toString is a primitive, do nothing.  Else,
            //    throw a type error
            def asPrimitive(e: Exp): (Seq[Stmt], Exp, Set[PVar]) = {
              val (eValueS, eValueE, ys1) = valueOf(e)
              val (eStringS, eStringE, ys2) =
                toSomething(eValueE, (e: Exp) => e, callToString)
              val (eFinalS, eFinalE, ys3) =
                toSomething(eStringE,
                            (e: Exp) => e,
                            (_: Var, _: Exp) => (throwTypeError, UndefAST(), Set()))
              (Seq(eValueS, eStringS, eFinalS),
               eFinalE, ys1 ++ ys2 ++ ys3)
            }

            val (e1eStmts, e1eFinalE, e1eys) = asPrimitive(e1e)
            val (e2eStmts, e2eFinalE, e2eys) = asPrimitive(e2e)

            withStatements(
              (asSeq(asSeq(interleave(e1eStmts, e2eStmts): _*),
		     makeIf(Binop(⌜≡⌝, Unop(Typeof, e1eFinalE),StrAST(STRING_TYPE)),
			    Assign(yRetval, Binop(⌜++⌝, e1eFinalE, isPrimToString(e2eFinalE))),
			    makeIf(Binop(⌜≡⌝, Unop(Typeof, e2eFinalE), StrAST(STRING_TYPE)),
				   Assign(yRetval, Binop(⌜++⌝, isPrimToString(e1eFinalE), e2eFinalE)),
				   Assign(yRetval, Binop(⌜+⌝, isPrimToNumber(e1eFinalE), isPrimToNumber(e2eFinalE)))))),
	       yRetval, e1eys ++ e2eys))
          }
	  case JSEqual =>
	    withStatementsExp(Binop(⌜≡⌝, e1e, e2e))
	  case JSNotEqual =>
	    withStatementsExp(Unop(⌞¬⌟, Binop(⌜≡⌝, e1e, e2e)))
	  case JSEquivalent =>
	    withStatementsExp(Binop(⌜≈⌝, e1e, e2e))
	  case JSNotEquivalent =>
	    withStatementsExp(Unop(⌞¬⌟, Binop(⌜≈⌝, e1e, e2e)))
	  case JSLessThan =>
	    lessThanCore(⌜≺⌝, ⌜<⌝)
	  case JSLessThanOrEqual =>
	    lessThanCore(⌜≼⌝, ⌜≤⌝)
	  case JSGreaterThan =>
	    lessThanCore(⌜≺⌝, ⌜<⌝, true)
	  case JSGreaterThanOrEqual =>
	    lessThanCore(⌜≼⌝, ⌜≤⌝, true)
	  case JSIn => {
	    // ECMA doesn't even try to convert to an object
            val (stringS, stringE, stringys) = toString(e1e)
            withStatements(
              (asSeq(stringS,
		     makeIf(Unop(IsPrim, e2e),
			    throwTypeError,
			    PVarMapper.noOpStatement)),
	       Binop(In, stringE, e2e), stringys))
          }

	  case JSInstanceOf => {
            // from Flanagan:
            // If the left hand side is not an object, return false.  The semantics
            // handle this already.  If the right hand side is not a function, throw
            // a type error.
	    withStatements(
              (asSeq(makeIf(Unop(⌞¬⌟, Binop(⌜≡⌝, Unop(Typeof, e2e), StrAST(FUNCTION_TYPE))),
                            throwTypeError,
                            PVarMapper.noOpStatement)),
	       Binop(InstanceOf, e1e, Binop(⌜⋆⌝, e2e, StrAST("prototype"))), Set()))
          }
	  case JSComma =>
	    withStatementsExp(e2e)
	  case JSLogAnd =>
	    logicalHelper(BoolAST(true))
	  case JSLogOr =>
	    logicalHelper(BoolAST(false))
	} // op match
      } // case JSBinop

      case JSUnop(op, e) => {
	val (es, ee, eys) = translate(e)
	
	def withStatement(t: TranslationRetval): TranslationRetval =
	  (asSeq(es, t._1), t._2, t._3 ++ eys)

	def withStatementExp(e: Exp): TranslationRetval =
	  (es, e, eys)

	def negationHelper(op: Uop): TranslationRetval = {
	  val (numberS, numberE, numberys) = toNumber(ee)
          withStatement(
            (numberS, Unop(op, numberE), numberys))
        }
	
	op match {
	  case JSVoid =>
	    withStatementExp(UndefAST())
	  case JSTypeof =>
	    withStatementExp(Unop(Typeof, ee))
	  case JSPlus =>
	    withStatement(toNumber(ee))
	  case JSMinus =>
	    negationHelper(⌞−⌟)
	  case JSBitNot =>
	    negationHelper(⌞~⌟)
	  case JSLogNot =>
	    withStatementExp(Unop(⌞¬⌟, toBool(ee)))
	  case JSToObj =>
	    withStatement(toObj(ee))
	}
      } // JSUnop

      case JSObject(fields) => {
	val (fieldNames, fieldSs, fieldEs, fieldys) = 
          unzip4(
            fields.map(
	      { case (JSStr(name), jsE) => {
	        val (fs, fe, fys) = translate(jsE)
	        (StrAST(name), fs, fe, fys) } } ))
	val (argsS, argsE, argsys) = makeArguments(Seq())
	val yRetval = freshScratch
	(asSeq(asSeq(fieldSs: _*),
	       argsS,
	       New(yRetval, PVarMapper.objectVar, argsE),
	       asSeq(fieldNames.zip(fieldEs).map(
		 { case (n, e) => Update(yRetval, n, e) }): _*)),
	 yRetval, flattenVars(fieldys) ++ argsys)
      }

      case JSArray(elements) => {
	val (elementsSs, elementsEs, elementsys) = elements.map(translate).unzip3
	val (argsS, argsE, argsys) = makeArguments(Seq())
	val yRetval = freshScratch
	(asSeq(asSeq(elementsSs: _*),
	       argsS,
	       makeNew(yRetval, PVarMapper.arrayVar, argsE),
	       asSeq(elementsEs.zip(0 until elementsEs.size).map(
		 { case (e, num) => Update(yRetval, StrAST(num.toString), e) } ): _*),
               Update(yRetval, StrAST(LENGTH_FIELD), NumAST(elementsEs.size))),
	 yRetval, flattenVars(elementsys) ++ argsys)
      }

      case JSThis() =>
	throw BadTransformation("Found 'this'")

      // if e1 is undef or null, throw a type error
      // if it's some other non-object, return true
      // else if it's an object, delete the given field from it
      case JSDelete(JSAccess(e1, e2)) => {
	val (e1S, e1E, e1ys) = translate(e1)
	val (e2S, e2E, e2ys) = translate(e2)
	val (fieldS, fieldE, fieldys) = toString(e2E)
	val yRetval = freshScratch
        (asSeq(e1S, e2S, fieldS,
               makeIf(Binop(⌜||⌝,
                            Binop(⌜≡⌝, e1E, UndefAST()),
                            Binop(⌜≡⌝, e1E, NullAST())),
                      throwTypeError,
                      makeIf(Binop(⌜≡⌝, Unop(Typeof, e1E), StrAST(OBJECT_TYPE)),
                             Del(yRetval, e1E, fieldE),
                             Assign(yRetval, BoolAST(true))))),
         yRetval, e1ys ++ e2ys ++ fieldys)
      }

      // delete for a non-Reference (where Reference is a meta-type specified
      // in ECMA)
      case JSDelete(e) => {
        val (s, _, ys) = translate(e)
        (s, BoolAST(true), ys)
      }

      case JSPrefixInc(v: JSVar) => 
	prefixVarHelper(v, 1.0)

      case JSPrefixInc(JSAccess(e1, e2)) => 
	prefixAccessHelper(e1, e2, 1.0)

      case JSPostfixInc(x: JSVar) => 
	postfixVarHelper(x, 1.0)

      case JSPostfixInc(JSAccess(e1, e2)) => 
	postfixAccessHelper(e1, e2, 1.0)

      case JSPrefixDec(v: JSVar) =>
	prefixVarHelper(v, -1.0)

      case JSPrefixDec(JSAccess(e1, e2)) =>
	prefixAccessHelper(e1, e2, -1.0)

      case JSPostfixDec(x: JSVar) =>
	postfixVarHelper(x, -1.0)

      case JSPostfixDec(JSAccess(e1, e2)) =>
	postfixAccessHelper(e1, e2, -1.0)

      case TransformDecl(_, _) =>
	throw BadTransformation("Encountered a TransformationDecl")

      case JSWhile(guard, body) => {
	val (sp, ep, ysp) = translate(guard)
	val (spp, _, yspp) = translate(body)
        val (sFinal, eFinal, ysFinal) = whileHelper(sp, ep, ep, spp, sp)
        (sFinal, eFinal, ysp ++ yspp ++ ysFinal)
      }

      case JSDoWhile(body, guard) => {
	val (sp, ep, ysp) = translate(guard)
	val (spp, _, yspp) = translate(body)
        val (sFinal, eFinal, ysFinal) = whileHelper(PVarMapper.noOpStatement,
                                                    BoolAST(true), ep,
                                                    spp, sp)
        (sFinal, eFinal, ysp ++ yspp ++ ysFinal)
      }

      case JSFor(initializer, guard, increment, body) => {
	val (s0p, _, s0ys) = translate(initializer)
	val (s1p, e1p, s1ys) = translate(guard)
	val (s2p, _, s2ys) = translate(increment)
	val (s3p, _, s3ys) = translate(body)
        val (sFinal, eFinal, ysFinal) = whileHelper(asSeq(s0p, s1p),
                                                    e1p, e1p,
                                                    s3p,
                                                    asSeq(s2p, s1p))
        (sFinal, eFinal, s0ys ++ s1ys ++ s2ys ++ s3ys ++ ysFinal)
      }
      
      case JSForIn(itervar, iterable, body) => {
	val (sp, ep, ysp) = translate(iterable)
        val (iterableObjS, iterableObjE, iterableObjys) = toObj(ep)
	val (spp, _, yspp) = translate(body)

        def itervarStmtToRetval(x: Var, beforeLabel: Stmt = PVarMapper.noOpStatement): TranslationRetval =
          (asSeq(sp,
                 iterableObjS,
                 makeLbl(BREAK_LABEL,
			 makeFor(x,
                                 iterableObjE,
                                 asSeq(beforeLabel,
                                       makeLbl(CONTINUE_LABEL, spp))))),
	   UndefAST(), ysp ++ iterableObjys ++ yspp)
          
        itervar match {
          case v: JSVar => 
            itervarStmtToRetval(PVarMapper.getVar(v))

          case JSAccess(e1, e2) => {
            val (objS, objE, objys) = translate(e1)
            val (fieldS, fieldE, fieldys) = translate(e2)
            val (accessS, obj, field, accessys) = accessSetup(objE, fieldE)
            val y = freshScratch
            val (finalS, finalE, finalys) = 
              itervarStmtToRetval(
                y,
                asSeq(
                  objS, fieldS, accessS,
                  Update(obj, field, y)))
            (finalS, finalE, objys ++ fieldys ++ accessys ++ finalys)
          }

          case _ => throw BadTransformation(
            "Unrecognized form in for-in iterator: " + itervar)
        }
      }
      
      case s@JSSeq(stmts) => {
        if (stmts.isEmpty) {
          if (s.isOrig) {
            (Decl(PVarMapper.INDICATE_JS_SEQUENCE, PVarMapper.noOpStatement), UndefAST(), Set())
          } else {
            noOpStatement(UndefAST())
          }
        } else {
	  val (ss, es, ys) = stmts.map(translate).unzip3
          val seq = asSeq(ss: _*)
          val vars = flattenVars(ys)
          if (s.isOrig) {
            (Decl(PVarMapper.INDICATE_JS_SEQUENCE, seq), es.last, vars)
          } else {
            (seq, es.last, vars)
          }
        }
      }

      case JSDecl(_) => 
	throw BadTransformation("JSDecl outside of start of function")

      case JSFunctionDecl(_, _, _) =>
	throw BadTransformation("JSFunctionDecl encountered")

      case JSIf(guard, ifTrue, ifFalse) => {
	val (sp, ep, ysp) = translate(guard)
	val (s1p, _, s1ys) = translate(ifTrue)
        val (s2p, _, s2ys) = translate(ifFalse.getOrElse(JSUndef()))
        (asSeq(sp, makeIf(toBool(ep), s1p, s2p)),
         UndefAST(), ysp ++ s1ys ++ s2ys)
      }

      case JSTry(tryBody, catchPart, finallyPart) => {
	val (tryS, _, tryys) = translate(tryBody)
	val (catchVar, catchS, catchys) =
	  catchPart match {
	    case Some((JSPVar(name), s)) => {
              val (sp, _, ys) = translate(s)
              (PVarMapper.getPVar(name), sp, ys)
            }
	    case _ => {
              val y = freshVar
              (y, Throw(y), Set(y))
            }
	  }
	val (finallyS, _, finallyys) = translate(finallyPart.getOrElse(JSUndef()))
	(makeTry(tryS, catchVar, catchS, finallyS),
         UndefAST(), tryys ++ catchys ++ finallyys)
      }

      case JSThrow(e) => {
	val (sp, ep, ys) = translate(e)
        (asSeq(sp, Throw(ep)), UndefAST(), ys)
      }

      case JSLabel(_) =>
	throw BadTransformation("Encountered a label on its own")

      case JSLabeledStmt(labels, body) => {
	val (sp, _, ysp) = translate(body)
	val s = labels.foldRight(sp)((cur, res) =>
	  makeLbl(cur.name, res))
	(s, UndefAST(), ysp)
      }

      case JSBreak(label) =>
	(Jump(optionLabel(label, BREAK_LABEL), UndefAST()), UndefAST(), Set())

      case JSContinue(label) =>
	(Jump(optionLabel(label, CONTINUE_LABEL), UndefAST()), UndefAST(), Set())

      case JSWith(_, _) =>
	throw BadTransformation("'with' is not yet implemented!")

      case JSReturn(exp) => {
	val (sp, ep, ys) = translate(exp.getOrElse(JSUndef()))
        // merge isn't needed here, since this will translate to something that puts us
	// at the end of the function
      	(asSeq(sp, Jump(RETURN_LABEL, ep)), UndefAST(), ys)
      }

      case JSSwitch(exp, cases, default) => {
	val (sp, ep, ysp) = translate(exp)
	val (spp, _, yspp) = default.map(translate).getOrElse(noOpRetval)
        // these need to live through JS statements, so they must be vars
	val y0 = freshVar
	val y1 = freshVar
	def handleCase(c: (JSExp, JSStmt)): (List[Stmt], Set[PVar]) = {
	  val (snp, enp, ysnp) = translate(c._1)
	  val (snpp, _, ysnpp) = translate(c._2)
	  (List(snp, makeIf(Binop(⌜||⌝, Binop(⌜≡⌝, enp, y0), y1),
			    asSeq(snpp, Assign(y1, BoolAST(true))),
			    PVarMapper.noOpStatement)), ysnp ++ ysnpp)
	}
        
        val (newCases, caseys) = 
          cases.foldRight((List[Stmt](), Set[PVar]()))((cur, res) => {
            val (stmts, ys) = handleCase(cur)
            (stmts ++ res._1, ys ++ res._2)
          })
            
	(makeLbl(BREAK_LABEL,
		 asSeq(sp,
		       Assign(y0, ep),
		       Assign(y1, BoolAST(false)),
                       asSeq(newCases: _*),
		       spp)),
	 UndefAST(), ysp ++ yspp ++ caseys ++ Set(y0, y1))
      }
    } // j match
} // Translator

