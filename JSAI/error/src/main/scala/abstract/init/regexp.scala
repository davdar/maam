// initial notJS state: RegExp

package notjs.abstracted.init

import notjs.syntax._
import notjs.abstracted.domains._
import notjs.abstracted.domains.AddressSpace._
import notjs.abstracted.traces.Trace
import notjs.abstracted.helpers.Helpers._
import notjs.abstracted.helpers.Fields
import notjs.abstracted.helpers.Errors._
import notjs.abstracted.init.Init._
import notjs.abstracted.init.InitHelpers._
import notjs.abstracted.init.StringHelpers._


object InitRegExp {

  // We often must return an array of matches;
  // an array of unknown strings is a suitable overapproximation.
  // TODO: factor something out with other (array) allocations, maybe?
  def allocUnknownStringArray(σ: Store, τ: Trace): (BValue, Store, Option[EValue]) = {
    // allocate the array
    val (σ1, arr_bv) = allocObj(Address.inject(Array_Addr), τ.toAddr, σ, τ)
    assert(arr_bv.as.size == 1, "freshly-allocated address set should have size 1")
    val arrayAddr_bv = Address.inject(arr_bv.as.head)
    // and make it unknown
    updateObj(arrayAddr_bv, Str.inject(Fields.length), Num.inject(NReal), σ1) match {
      case (Some((_, σ2)), err1) ⇒
        updateObj(arrayAddr_bv, Str.inject(SNum), Str.inject(STop) ⊔ Undef.BV, σ2) match {
          case (Some((_, σ3)), _) ⇒ (arrayAddr_bv, σ3, err1)
          case _ ⇒ sys.error("error in making new array's entries unknown")
        }
      case _ ⇒ sys.error("error in making new array's length unknown")
    }
  }

  /* Some methods may mutate the lastIndex field of RegExps with the `global` property set. */
  // TODO: can increase precision by filtering for RegExp objects
  def mutateLastIndex(addrs: Addresses, σ: Store): Store =
    addrs.foldLeft[Store](σ) {
      case (σ_acc, a) ⇒ σ_acc ⊔
        σ.putObj(a, σ.getObj(a, Str.⊥) + (Str.α("lastIndex") → Num.inject(NReal)), Str.α("lastIndex"))
    }

  // also used in some String.prototype methods
  def matchBody(regexp_as: Addresses, σ: Store, τ: Trace): Set[(Value, Store)] = {
    val (arr_a_bv, σ_, err) = allocUnknownStringArray(σ, τ)
    Set((arr_a_bv ⊔ Null.BV, mutateLastIndex(regexp_as, σ_))) ++ (err match {
      case Some(bv) ⇒ Set((bv, σ_))
      case None ⇒ Set()
    })
  }

  val Internal_RegExp_afterToString =
    (bvs: List[BValue], x: Var, ρ: Env, σ: Store, ß:Scratchpad, κ: KStack, τ: Trace) ⇒ {
      // bvs should contain address of object to populate at head
      val re_addr_bv = bvs(0)
      assert(re_addr_bv.as.size == 1,
        "RegExp: address set of fresh RegExp object should be of size 1")
      val re_addr = re_addr_bv.as.head
      val old_obj = σ getObj( re_addr, Str.⊥ )
      val re_obj = old_obj copy (
        intern = old_obj.intern ++ Map[Str, Any](
          Str.α("source") → Str.inject(STop),
          Str.α("global") → Bool.inject(BTop),
          Str.α("ignoreCase") → Bool.inject(BTop),
          Str.α("multiline") → Bool.inject(BTop),
          Str.α("lastIndex") → Num.inject(Num.α(0))
        )
      )

      makeState(re_addr_bv, x, ρ, σ putObj(re_addr, re_obj), ß, κ, τ)
    }
  val RegExp_Obj = createInitFunctionObj(
    Native(
      (selfAddr: BValue, argArrayAddr: BValue, x: Var, ρ: Env, σ: Store, ß:Scratchpad, κ: KStack, τ: Trace) ⇒ {
        assert(argArrayAddr.defAddr, "RegExp: Arguments array address set should refer to addresses")
        assert(argArrayAddr.as.size == 1, "RegExp: Arguments array address set should contain a single address")
        val argsArray = σ getObj argArrayAddr.as.head

        // it is safe to use undef for missing arguments here.
        val argList: List[(BValue, ConversionHint)] = List.range(0, 2) map {
          i ⇒ (argsArray(Str.α(i.toString)) getOrElse Undef.BV, StringHint)
        }

        // If we are not called as a constructor, we must allocate ourself
        val calledAsConstr = argsArray.intern.getOrElse(Fields.constructor, false).asInstanceOf[Boolean]
        val (σ_, re_addr_bv) = if (calledAsConstr)
          allocObj(Address.inject(RegExp_Addr), τ.toAddr, σ, τ)
        else // otherwise, our address is selfAddr
          (σ, selfAddr)

        /* we must convert all arguments to strings, and pass the address
           of the object to populate */
        val ςs_success = Convert(
          (re_addr_bv, NoConversion) :: argList,
          Internal_RegExp_afterToString,
          x, ρ, σ_, ß, κ, τ )

        /* RegExp construction could also result in a TypeError or SyntaxError */
        val ςs_error = makeState(EValue(typeError.bv ⊔ syntaxError.bv), x, ρ, σ, ß, κ, τ)

        ςs_success ++ ςs_error
      }
    ),
    Map(
      "length" → Num.inject(Num.α(2)),
      "prototype" → Address.inject(RegExp_prototype_Addr)
    )
  )

  val RegExp_prototype_Obj = createInitObj(
    Map(
      "constructor" → Address.inject(RegExp_Addr),
      "exec" → Address.inject(RegExp_prototype_exec_Addr),
      "test" → Address.inject(RegExp_prototype_test_Addr),
      "toString" → Address.inject(RegExp_prototype_toString_Addr),
      // RegExp.prototype is a RegExp object, identical to the result of new RegExp()
      "source" → Str.inject(Str.α("")),
      "global" → Bool.inject(BFalse),
      "ignoreCase" → Bool.inject(BFalse),
      "multiline" → Bool.inject(BFalse),
      "lastIndex" → Num.inject(Num.α(0))
    ),
    Map(Fields.classname → CRegexp)
  )

  val RegExp_prototype_exec_Obj =
    usualFunctionObj(ezSig(NoConversion, List(StringHint))) {
      case (List(self, _), σ, τ) ⇒ matchBody(self.as, σ, τ)
      case _ ⇒ sys.error("RegExp.prototype.exec: arguments nonconformant to signature")
    }

  val RegExp_prototype_test_Obj =
    usualFunctionObj(ezSig(NoConversion, List(StringHint))) {
      case (List(self, _), σ, τ) ⇒ matchBody(self.as, σ, τ) map {
        case (bv:BValue, σ_) ⇒ {
          val res: Bool = 
            if (bv.nil == Null.⊥) BTrue
            else if (bv.defNull) BFalse
            else BTop

          (Bool.inject(res), σ_)
        }
        case (v, σ_) ⇒ (v, σ_)
      }
      case _ ⇒ sys.error("RegExp.prototype.test: arguments nonconformant to signature")
    }

  val RegExp_prototype_toString_Obj =
    constFunctionObj(ezSig(NoConversion, List()), Str.inject(STop))

}
