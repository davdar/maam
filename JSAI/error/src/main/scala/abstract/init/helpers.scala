// Helpers for initial notJS state

package notjs.abstracted.init

import notjs.syntax._
import notjs.abstracted.domains._
import notjs.abstracted.domains.AddressSpace._
import notjs.abstracted.traces.Trace
import notjs.abstracted.init.StringHelpers._
import notjs.abstracted.helpers.Helpers._
import notjs.abstracted.helpers.Errors._
import notjs.abstracted.helpers.Fields
import notjs.abstracted.interpreter.State
import notjs.abstracted.interpreter.notJS
import notjs.abstracted.init.Init._


object InitHelpers {

  /* Often, methods in the initial state have to implicitly convert their
     arguments' types, the process of which may involve calling user-defined
     conversion methods.  To this end, we provide the function `Convert` and
     the ConversionHint trait, which assist in the implementation of
     such methods. */
  /* In particular, a ConversionHint can avoid triggering conversion, attempt
     to convert to a number, or attempt to convert to a string. */
  sealed trait ConversionHint
  case object NoConversion extends ConversionHint
  sealed trait PrimHint extends ConversionHint
  case object StringHint extends PrimHint
  case object NumberHint extends PrimHint

  /* Convert itself takes a list of base values to convert and information
     on how to convert them, some function to call with the converted values,
     and the rest of the information required to build states.  We avoid
     closing over this in the final function to be called, since it may need
     to be traced if GC is triggered in the process of conversion. */
  /* TODO/FIXME: handles only easy case with all conversions handled
     by native code; aborts instead of entering user code.
     additionally, aborts rather than properly throwing TypeError,
     as the complexity that would introduce is best handled along with
     user code */
  def Convert
    ( l: List[(BValue, ConversionHint)],
      f: (List[BValue], Var, Env, Store, Scratchpad, KStack, Trace) ⇒ Set[State],
      x: Var, ρ: Env, σ: Store, ß:Scratchpad, κ: KStack, τ: Trace ): Set[State] = {

    /* convPrim: assuming bv is a primitive value, convert to a primitive
       by given hint */
    def convPrim(hint: PrimHint)(bv: BValue) = hint match {
      case NumberHint ⇒ bv.tonum
      case StringHint ⇒ bv.tostr
    }

    /* convBValue: convert single base value by given hint, accounting
       for both its primitive component and any object addresses it may
       contain. */
    def convBValue(hint: PrimHint, bv: BValue): (BValue, Boolean) =
      bv.as.map(convObj(hint)).foldLeft[(BValue, Boolean)]((convPrim(hint)(bv), false))(
        (a, b) ⇒ (a._1 ⊔ b._1, a._2 || b._2))

    /* convObj: convert object at address by given hint */
    def convObj(hint: PrimHint)(a: Address): (BValue, Boolean) = {
      /* If given NumberHint, attempt conversion first by valueOf,
         and if given StringHint, attempt first by toString;
         if our primary choice could fail, we must perform conversion
         by the other method as well and join the results. */
      lazy val valueOf = lookup(Set(a), Str.α("valueOf"), σ)
      lazy val toString = lookup(Set(a), Str.α("toString"), σ)
      val o = σ getObj (a, Str.⊥)

      // TODO: ensure these coincide with their respective function objects,
      // perhaps by factoring the commonality out.
      lazy val values = valueOf.as map { av ⇒ av match {
        case `Number_prototype_valueOf_Addr` ⇒ o.getValue
        case `String_prototype_valueOf_Addr` ⇒ o.getValue
        case `Boolean_prototype_valueOf_Addr` ⇒ o.getValue
        case `Date_prototype_valueOf_Addr` ⇒ Num.inject(NReal)
        case `Object_prototype_valueOf_Addr` ⇒ Address.inject(a)
        case addr if (σ getObj (addr, Str.⊥)).getCode.nonEmpty ⇒ BValue.⊥ // TODO: print a warning
        case _ ⇒ BValue.⊥
      } }

      lazy val strings = toString.as map { av ⇒ av match {
        case `Number_prototype_toString_Addr` ⇒ o.getValue.tostr
        case `String_prototype_toString_Addr` ⇒ o.getValue
        case `Boolean_prototype_toString_Addr` ⇒ o.getValue.tostr
        case `Object_prototype_toString_Addr` ⇒ Str.inject(SNotNum).tostr // TODO: Can be more precise
        case `Array_prototype_toString_Addr` ⇒ {
          // lookup the indices of the array, convert them to strings
          // then throw them away, we were just making sure the conversions
          // would not trigger any asserts
          // TODO: we can be more precise here
          convBValue(StringHint, lookup(Set(a), SNum, σ))
          Str.inject(STop).tostr
        }
        case `Date_prototype_toString_Addr` ⇒ Str.inject(SNotNum).tostr
        case `Function_prototype_toString_Addr` ⇒ Str.inject(SNotNum).tostr
        case addr if (σ getObj (addr, Str.⊥)).getCode.nonEmpty ⇒ BValue.⊥ // TODO: print a warning
        case _ ⇒ BValue.⊥
      } }

      lazy val numconv = (valueOf, values)
      lazy val strconv = (toString, strings)

      val (primaryConversion, primaryConverted) = hint match {
        case NumberHint ⇒ numconv
        case StringHint ⇒ strconv
      }
      lazy val (secondaryConversion, secondaryConverted) = hint match {
        case NumberHint ⇒ strconv
        case StringHint ⇒ numconv
      }

      /* After calling conversions, convert result to the desired final form.
         TODO: this currently makes the assumption that we always get a primitive
         from our conversion methods, since we do not currently handle user code;
         when revising, be sure to correctly handle user failure to return a
         primitive value. */
      def convPrims(bvs: Set[BValue]): BValue =
        bvs.map(convPrim(hint)).foldLeft(BValue.⊥)(_ ⊔ _)

      (convPrims(primaryConverted) ⊔
        (if (primaryConversion.defAddr) BValue.⊥ else
           convPrims(secondaryConverted)), 
        !secondaryConversion.defAddr)
    }

    val prims = l map {
      case (bv, NoConversion) ⇒ (bv, false)
      case (bv, hint:PrimHint) ⇒ convBValue(hint, bv)
    }
    
    f(prims.map(_._1), x, ρ, σ, ß, κ, τ) ++ 
      (if (prims.map(_._2).exists(x ⇒ x)) 
        makeState(typeError, x, ρ, σ, ß, κ, τ)
        else Set[State]())
  }

  def ToNumber(l: List[BValue], f: (List[BValue], Var, Env, Store, Scratchpad, KStack, Trace) ⇒ Set[State], x: Var, ρ: Env, σ: Store, ß:Scratchpad, κ: KStack, τ:Trace): Set[State] =
    Convert(l.map(e ⇒ (e, NumberHint)), f, x, ρ, σ, ß, κ, τ)

  def ToString(l: List[BValue], f: (List[BValue], Var, Env, Store, Scratchpad, KStack, Trace) ⇒ Set[State], x: Var, ρ: Env, σ: Store, ß:Scratchpad, κ: KStack, τ:Trace): Set[State] =
    Convert(l.map(e ⇒ (e, StringHint)), f, x, ρ, σ, ß, κ, τ)

  def createInitObj(fields: Map[String, BValue], internal: Map[Str, Any] = Map()): Object = {
    val internalFieldMap = if (!internal.contains(Fields.proto))
      internal + (Fields.proto → Address.inject(Object_prototype_Addr))
    else
      internal

    val internalFieldMap1 = if (!internal.contains(Fields.classname))
      internalFieldMap + (Fields.classname → CObject)
    else
      internalFieldMap

    createInitObjCore(fields, internalFieldMap1)
  }

  def createInitFunctionObj(clo: Native, fields: Map[String, BValue], internal: Map[Str, Any] = Map(), cls: JSClass = CFunction): Object = {
    assert(fields contains "length", "functions must have length property")
    val internalFieldMap = internal ++ Map(
      Fields.proto → Address.inject(Function_prototype_Addr),
      Fields.code → Set(clo),
      Fields.classname → cls
    )

    createInitObjCore(fields, internalFieldMap)
  }

  def createObj(external: ExternMap = ExternMap(), internal: Map[Str, Any] = Map(), present: Set[Str] = Set()): Object = {
    val internalFieldMap = if (!internal.contains(Fields.proto))
      internal ++ Map(Fields.proto → Address.inject(Object_prototype_Addr))
    else
      internal

    val internalFieldMap1 = if (!internal.contains(Fields.classname))
      internalFieldMap ++ Map(Fields.classname → CObject)
    else
      internalFieldMap

    val present1 = (external.exactnotnum.keys ++ external.exactnum.keys).foldLeft(present)(_ + _)

    Object(external, internalFieldMap1, present1)
  }

  /* TODO: does anything use x or ρ?  If not, this really should be factored
     out somewhere else, since passing them around everywhere is...suboptimal. */
  def makeState(v: Value, x: Var, ρ: Env, σ: Store, ß:Scratchpad, κ: KStack, τ: Trace): Set[State] = {
    v match {
      case bv:BValue ⇒ x match {
        case pv:PVar ⇒ Set(State( v, ρ, σ + (ρ(pv) → bv), ß, κ, τ ))
        case sc:Scratch ⇒
          Set(State( v, ρ, σ, ß(sc) = bv, κ, τ ))
      }
       case _ ⇒ Set(State( v, ρ, σ, ß, κ, τ ))
    }
  }


  // TODO: All of the special classes.
  // TODO: isCallable

  // if shouldError, the value returned can be typeError (on null or undef).
  // performs JavaScript type conversion, returning a BValue containing only addresses and/or a typeError, plus a new store
  // probably should use allocObj

  def isNumberClass(j: JSClass): Boolean = j == CNumber // TODO. either CNumber or Number.prototype

  def isStringClass(j: JSClass): Boolean = j == CString // TODO. either CString or String.prototype


  /* Many methods follow a common pattern, where they require some type conversions,
     and have a `length` property describing number of arguments typically taken.
     A UsualSignature describes the type conversions required in a method,
     as well as how many arguments it takes. */
  sealed trait UsualSignature { def lengthProperty: Int }
  /* For functions taking a fixed number of arguments, Sig provides a conversion
     hint for the self object and each positional argument, in addition to the
     length property. */
  case class Sig(selfHint: ConversionHint, argHints: List[ConversionHint], lengthProperty: Int) extends UsualSignature
  /* For variadic functions, VarSig provides a conversion hint for the self
     object and a single hint for all arguments.  Thus far this has proven sufficient. */
  case class VarSig(selfHint: ConversionHint, argsHint: ConversionHint, lengthProperty: Int) extends UsualSignature

  /* Many methods with a signature follow a further pattern as well:
     throw a type error if called as a constructor, convert all arguments
     specified by their signature, treat unspecified arguments as `undefined`,
     and set the `length` property. */
  /* So far this has proven useful, but it does not handle all cases; please
     factor anything out if it would be desirable in these unhandled cases. */
  /* Given a signature, sigFunctionObj creates a function object with this
     desired behavior, with the body implemented by a provided Scala function,
     which may then assume its argument has been properly converted, etc. */
  def sigFunctionObj(sig: UsualSignature)(f: (List[BValue], Var, Env, Store, Scratchpad, KStack, Trace) ⇒ Set[State]): Object = {

    createInitFunctionObj(Native(
        (selfAddr: BValue, argArrayAddr: BValue, x: Var, ρ: Env, σ: Store, ß:Scratchpad, κ: KStack, τ: Trace) ⇒ {
          assert(argArrayAddr.defAddr, "Internal function object: argument array address must be an address")
          assert(argArrayAddr.as.size == 1, "Internal function object: argument array address set size must be 1")
          val argsArray = σ.getObj(argArrayAddr.as.head, Str.⊥)
          // true iff invoking as a constructor:
          val construct = argsArray.intern.getOrElse(Fields.constructor, false).asInstanceOf[Boolean]
          if (construct)
            makeState(typeError, x, ρ, σ, ß, κ, τ)
          else {
            val argsList: List[(BValue, ConversionHint)] = sig match {
              case Sig(selfHint, argHints, _) ⇒ {
                (selfAddr → selfHint) :: List.range(0, argHints.length).zip(argHints).map {
                  case (i, hint) ⇒ (argsArray(Str.α(i.toString)) getOrElse Undef.BV, hint)
                }
              }
              case VarSig(selfHint, argsHint, _) ⇒ {
                List((selfAddr → selfHint), ((argsArray(SNum) getOrElse Undef.BV) → argsHint))
              }
            }

            Convert(argsList, f, x, ρ, σ, ß, κ, τ)
          }
        }
      ),
      Map(
        "length" → Num.inject(Num.α(sig.lengthProperty))
      )
    )
  }

  /* Furthermore, it is usually the case that these methods do not require the
     environment, scratchpad, assignee variable, or continuation stack, so we
     can thread them through here.
     The store is useful here for accesses and updates, and the trace for
     allocations. */
  def usualFunctionObj(sig: UsualSignature)(f: (List[BValue], Store, Trace) ⇒ Set[(Value, Store)]): Object =
    sigFunctionObj(sig) {
      (bvs: List[BValue], x: Var, ρ: Env, σ: Store, ß:Scratchpad, κ: KStack, τ: Trace) ⇒
        f(bvs, σ, τ) flatMap {
          case (v, σ_) ⇒ makeState(v, x, ρ, σ_, ß, κ, τ)
        }
    }

  /* Many usual methods also don't touch the store after conversions, in which
     case we can implement function objects only in terms of a signature and a
     function from a list of (converted) argument BValues to a set of Values. */
  def pureFunctionObj(sig: UsualSignature)(f: List[BValue] ⇒ Set[Value]): Object =
    usualFunctionObj(sig) { case (bvs, σ, τ) ⇒ f(bvs).map(bv ⇒ (bv, σ)) }

  // for poor approximations and unmodelable functions,
  // simply convert arguments for side-effects and throw away the result
  def constFunctionObj(sig: UsualSignature, v: Value): Object =
    pureFunctionObj(sig)(_ ⇒ Set(v))

  // "easy" signatures have length equal to the length of their argHints
  // list; some methods don't have this property!
  def ezSig(selfHint: ConversionHint, argHints: List[ConversionHint]) =
    Sig(selfHint, argHints, argHints.length)


  /* For constructors like String and Number which amount to performing checks
     and setting the `value` internal property, we can factor out the common
     behavior after the point of type conversions quite easily.
     The genValueObjConstructor method will, given a constructor name (to blame in
     assertion) and a function to perform additional checks/transforms on the (converted)
     argument recieved by the constructor, produce a function suited for passing
     to Convert.  In particular, it expects its argument list to be of the form
     List(addr, val) where addr is the address of the object allocated by `new`,
     and `val` is the value provided for storage in the `value` internal property. */
  def genValueObjConstructor(cname: String)(bvtrans: BValue ⇒ BValue) =
    (bvs: List[BValue], x: Var, ρ: Env, σ: Store, ß:Scratchpad, κ: KStack, τ: Trace) ⇒ {
      assert(bvs.length >= 2,
        cname + " constructor: should have `self` address plus 1 argument by this point")
      val (selfAddr_bv, arg_value) = (bvs(0), bvs(1))
      assert(selfAddr_bv.defAddr,
        "String constructor: `self` address should be an address, always")
      assert(selfAddr_bv.as.size == 1,
        "String constructor: `self` address set should be singleton")
      val selfAddr = selfAddr_bv.as.head
      val final_value = bvtrans(arg_value)

      /* in constructors, an object has been allocated at selfAddr for us to populate */
      val old_self = σ getObj (selfAddr, Str.⊥)
      val new_self = old_self copy (intern = old_self.intern + (Fields.value → final_value))
      
      // special case when we have a string constructor
      val newer_self = 
        if (cname == "String") {
          val exactStr = Str.getExact(final_value.str)
          val extern = exactStr match {
            case Some(s) ⇒ List.range(0, s.length).foldLeft(
              new_self.extern ++ (Fields.length → Num.inject(Num.α(s.length))))(
                (acc, e) ⇒ acc ++ (Str.α(e.toString) → Str.inject(Str.α(s(e).toString))))
            case None ⇒ (new_self.extern + (Fields.length → Num.inject(NReal))) + (SNum → Str.inject(Str.SingleChar))
          }
          new_self copy (extern = extern, present = new_self.present + Fields.length)
        } else new_self

      makeState(selfAddr_bv, x, ρ, σ putObj(selfAddr, newer_self), ß, κ, τ)
    }
  /* most of the time no transformation is needed, just checks */
  def valueObjConstructor(cname: String)(verify: BValue ⇒ Unit) =
    genValueObjConstructor(cname) { bv ⇒
      verify(bv)
      bv
    }

  /* many prototypes define toString and valueOf methods which cannot be used
     on values which are not members of the corresponding class.
     toPrimHelper acts as a general mechanism for defining these methods;
     it takes the address of the object on which the respective method is called,
     the appropriate class-checker and conversions to perform, and returns both
     a set of successful results and of possible exceptions. */
  def toPrimHelper[A](selfAddr: BValue, σ: Store, goodClass: JSClass ⇒ Boolean,
    conv: BValue ⇒ A, bottom: A)(join: (A, A) ⇒ A): (Set[A], Set[EValue]) = {

    assert(selfAddr.defAddr, "Assuming selfAddr is always addresses")

    val selves: Set[Object] = selfAddr.as.map(σ.getObj(_, Str.⊥))
    val (goods, bads) = selves partition { self ⇒ goodClass(self.myClass) }

    val goodv = goods.foldLeft[A](bottom) {
      case (acc, self) ⇒ join(acc, conv(self.getValue))
    }

    val good_res: Set[A] = if (goodv == bottom) Set() else Set(goodv)
    val err_res: Set[EValue] = if (bads.isEmpty) Set() else Set(typeError)

    (good_res, err_res)
  }

  /* Additionally, in most cases, the entire rest of these methods may be
     described by usualFunctionObject */
  def usualToPrim[A](goodClass: JSClass ⇒ Boolean,
                     conv: BValue ⇒ A, 
                     bottom: A, 
                     inject: A ⇒ Value)(join: (A, A) ⇒ A) = {      
      usualFunctionObj(ezSig(NoConversion, List())) {
        case (List(selfAddr), σ, _) ⇒ {
          val (goods, errs) = toPrimHelper[A](selfAddr, σ, goodClass, conv, bottom)(join)
          (goods.map(inject) ++ errs.map(ev ⇒ ev:Value)) map { (_, σ) }
        }
        case _ ⇒ sys.error("usualToPrimHelper: signature nonconformance")
      }
    }

  def dangleMap(m: Map[String, BValue]): Map[String, BValue] = {
    if (notJS.Mutable.dangle) m else Map()
  }


  def unimplemented(name: String): Object = createInitFunctionObj(Native(
    (selfAddr: BValue, argArrayAddr: BValue, x: Var, ρ: Env, σ: Store, ß:Scratchpad, κ: KStack, τ:Trace) ⇒ {
      sys.error(name + ": Not implemented")
    }
  ), Map("length" → Num.inject(Num.α(0))))

}
