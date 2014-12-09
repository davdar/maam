// notJS initial state: Array-like objects

package notjs.abstracted.init

import notjs.syntax._
import notjs.abstracted.domains._
import notjs.abstracted.domains.AddressSpace._
import notjs.abstracted.traces.Trace
import notjs.abstracted.helpers.Helpers._
import notjs.abstracted.helpers.Errors._
import notjs.abstracted.helpers.Fields
import notjs.abstracted.init.InitHelpers._
import notjs.abstracted.init.Init._
import notjs.abstracted.init.StringHelpers._


object InitArrays {

  val Array_Obj = createInitFunctionObj(Native(
    (selfAddr: BValue, argArrayAddr: BValue, x: Var, ρ: Env, σ: Store, ß:Scratchpad, κ: KStack, τ:Trace) ⇒ {
      assert(argArrayAddr.defAddr, "Arguments array refers to non-addresses")
      assert(argArrayAddr.as.size == 1, "Arguments array refers to multiple addresses")

      val argsObj = σ.getObj(argArrayAddr.as.head, Str.⊥)
      val argLength = argsObj(Fields.length).getOrElse(BValue.⊥).n
      assert(argLength != Num.⊥, "When constructing an array, arguments length should be provided")

      // true iff invoking as a constructor:
      val calledAsConstr = argsObj.intern.getOrElse(Fields.constructor, false).asInstanceOf[Boolean]
      /* Array behaves the same when called as a constructor and function,
         so the differences between the following codepaths are to compensate for the
         difference between method calls and constructor invocations in notJS. */
      val (σ1, arrayAddrs) = if (calledAsConstr) {
        // we should have already got an array allocated, the rest will be taken care of
        // by their respective constructor functions
        val arrayAddrs = selfAddr.as.filter(a ⇒ σ.getObj(a, Str.⊥).getJSClass == CArray)
        (σ, arrayAddrs)
      } else {
        // called as a function: first, construct the array object
        val (σ1, bv) = allocObj(Address.inject(Array_Addr), τ.toAddr, σ, τ)
        (σ1, bv.as)
      }
      assert(arrayAddrs.size == 1, "We should have allocated one and only one address for arrays")
      val arrayAddr = arrayAddrs.head
      val oldArrayObj = σ1 getObj( arrayAddr, Str.⊥ )

      val (argLenMaybe1, argLenMaybeNot1) = argLength match {
        case NConst(d) if (d.toInt == 1) ⇒ (true, false)
        case NConst(d) ⇒ (false, true)
        case _ ⇒ (true, true)
      }
      val extractedArgLength: Option[Int] = argLength match {
        case NConst(d) ⇒ Some(d.toInt)
        case _ ⇒ None
      }
      val arg0 = argsObj(Str.α("0")).getOrElse(Undef.BV)
      val arg0MaybeNumeric = arg0.sorts(DNum)
      val arg0MaybeNotNumeric = !arg0.defNum

      /*    
         First, the "empty array with length set to a number" case should only
         apply when the singular argument is numeric (do not convert it);
         otherwise, a new array should be created as in the case of # of args
         not equal to one.
         Furthermore, the length property should be set to the argument provided,
         not the length of the arguments array. */

      val ones = if (argLenMaybe1 && arg0MaybeNumeric) {
        val (noexc, exc) = updateObj(Address.inject(arrayAddr), Str.inject(Fields.length), arg0.onlyNum, σ1)
        val s1 = noexc match {
          case Some((bv, σ2)) ⇒ {
            makeState(Address.inject(arrayAddr), x, ρ, σ2, ß, κ, τ)
          }
          case None ⇒ Set()
        }
        val s2 = exc match {
          case Some(ev) ⇒ makeState(ev, x, ρ, σ1, ß, κ, τ)
          case None ⇒ Set()
        }
        s1 ++ s2
      } else Set()

      val notones = if (argLenMaybeNot1 || arg0MaybeNotNumeric) {
        val updatedArrObj = extractedArgLength match {
          case Some(knownArgLength) ⇒ {
            newArray(Num.α(knownArgLength), List.range(0, knownArgLength).map(n ⇒ argsObj(Str.α(n.toString)).getOrElse(Undef.BV)), None, oldArrayObj, false)
          }
          case None ⇒ // arg length maybe 1, but it is not known exactly how much
            newArray(argLength, List(), argsObj.extern.num, oldArrayObj, false)
        }
        makeState(Address.inject(arrayAddr), x, ρ, σ1.putObj(arrayAddr, updatedArrObj), ß, κ, τ)
      } else Set()

      ones ++ notones
    }),
    fields = Map(
      "prototype" → Address.inject(Array_prototype_Addr),
      "length" → Num.inject(Num.α(1))) ++ dangleMap(Map(
        "isArray" → Address.inject(Array_isArray_Addr)
      )
    ), cls = CArray_Obj
  )

  val Array_prototype_Obj = createInitObj(
    Map(
      "constructor" → Address.inject(Array_Addr),
      "length" → Num.inject(Num.α(0)),
      "concat" → Address.inject(Array_prototype_concat_Addr),
      "indexOf" → Address.inject(Array_prototype_indexOf_Addr),
      "join" → Address.inject(Array_prototype_join_Addr),
      "lastIndexOf" → Address.inject(Array_prototype_lastIndexOf_Addr),
      "pop" → Address.inject(Array_prototype_pop_Addr),
      "push" → Address.inject(Array_prototype_push_Addr),
      "reverse" → Address.inject(Array_prototype_reverse_Addr), // TODO
      "shift" → Address.inject(Array_prototype_shift_Addr), // TODO
      "sort" → Address.inject(Array_prototype_sort_Addr),
      "splice" → Address.inject(Array_prototype_splice_Addr),
      "toString" → Address.inject(Array_prototype_toString_Addr) // TODO
    ) ++ dangleMap(Map(
      "every" → Address.inject(Array_prototype_every_Addr), // TODO
      "filter" → Address.inject(Array_prototype_filter_Addr), // TODO
      "forEach" → Address.inject(Array_prototype_forEach_Addr), // TODO
      "map" → Address.inject(Array_prototype_map_Addr), // TODO
      "reduce" → Address.inject(Array_prototype_reduce_Addr), // TODO
      "reduceRight" → Address.inject(Array_prototype_reduceRight_Addr), // TODO
      "slice" → Address.inject(Array_prototype_slice_Addr), // TODO
      "some" → Address.inject(Array_prototype_some_Addr), // TODO
      "toLocaleString" → Address.inject(Array_prototype_toLocaleString_Addr), // TODO
      "unshift" → Address.inject(Array_prototype_unshift_Addr) // TODO
    )),
    Map(Fields.classname → CArray_prototype_Obj)
  )

  val Array_prototype_join_Obj = createInitFunctionObj(Native(
    (selfAddr: BValue, argArrayAddr: BValue, x: Var, ρ: Env, σ: Store, ß:Scratchpad, κ: KStack, τ:Trace) ⇒ {
      assert(argArrayAddr.defAddr, "Arguments array refers to non-addresses")
      assert(argArrayAddr.as.size == 1, "Arguments array refers to multiple addresses")
      val lenVal = lookup(selfAddr.as, Fields.length, σ)
      val argsObj = σ getObj( argArrayAddr.as.head, Str.α("0") )
      val separator = argsObj(Str.α("0")) getOrElse Str.inject(Str.α(","))
      if (lenVal == Num.inject(Num.α(0)))
        makeState(Str.inject(Str.α("")), x, ρ, σ, ß, κ, τ)
      else {
        val summaryVal = lookup(selfAddr.as, SNum, σ)
        ToString(List[BValue](separator, summaryVal), // call tostring on each of these
                (l: List[BValue], x: Var, ρ: Env, σ: Store, ß:Scratchpad, κ: KStack, τ: Trace) ⇒ {
                  // then return STop
                  makeState(Str.inject(STop), x, ρ, σ, ß, κ, τ)
                }, x, ρ, σ, ß, κ, τ)
      }
    }
  ), Map("length" → Num.inject(Num.α(1))))

  val Array_prototype_pop_Obj = createInitFunctionObj(Native(
    (selfAddr: BValue, argArrayAddr: BValue, x: Var, ρ: Env, σ: Store, ß:Scratchpad, κ: KStack, τ:Trace) ⇒ {
      val lenVal = lookup(selfAddr.as, Fields.length, σ)

      // TODO: answer: can we assume `length` does not need type conversion?
      val zeroς = if (lenVal.n.defNot0) Set() else makeState(Undef.BV, x, ρ, σ, ß, κ, τ)

      // we choose to throw a type error if called on a non-array
      val arrayAddrs = selfAddr.as.filter(a ⇒ σ.getObj(a, Str.⊥).getJSClass == CArray)
      
      if (arrayAddrs.size != selfAddr.as.size)
          makeState(typeError, x, ρ, σ, ß, κ, τ)
      else {
        val arrayAddr = arrayAddrs.head
        val oldArrayObj = σ getObj( arrayAddr, Str.⊥ )
        // TODO: precision if length known?
        val summaryVal = lookup(arrayAddrs, SNum, σ)
        val updatedArrObj = newArray(NReal, List(), Some(summaryVal), oldArrayObj, true)
        val nonzeroς =
          if (lenVal.n.def0)
            Set()
          else
            makeState(summaryVal, x, ρ, σ.putObj(arrayAddr, updatedArrObj), ß, κ, τ)

        zeroς ++ nonzeroς 
      }
    }
  ), Map("length" → Num.inject(Num.α(1))))

  val Array_prototype_push_Obj = createInitFunctionObj(Native(
    (selfAddr: BValue, argArrayAddr: BValue, x: Var, ρ: Env, σ: Store, ß:Scratchpad, κ: KStack, τ:Trace) ⇒ {
      assert(argArrayAddr.defAddr,
        "Array.prototype.push: Arguments array should refer to addresses")
      assert(argArrayAddr.as.size == 1,
        "Array.prototype.push: Arguments array should refer to a single address")

      // we choose to throw a type error if called on a non-array
      /* TODO: if this sort of thing is a common pattern, factor it out
         into a helper */
      /* TODO: additionally, check if we care about anything which has
         non-TypeError behavior, and if so, account for that. */
      val arrayAddrs = selfAddr.as.filter(a ⇒ σ.getObj(a, Str.⊥).getJSClass == CArray)
      val errς =
        if (arrayAddrs.size != selfAddr.as.size)
          makeState(typeError, x, ρ, σ, ß, κ, τ)
        else
          Set()

      val isStrong = arrayAddrs.size == 1 && σ.isStrong(arrayAddrs.head)    
      val σ1 = arrayAddrs.foldLeft(σ) {
        case (acc, arrayAddr) ⇒ {
          val oldArrayObj = acc getObj( arrayAddr, Str.⊥ )
          // TODO: precision if length known?
          val summaryVal = lookup(Addresses(arrayAddr), SNum, acc) ⊔ lookup(argArrayAddr.as, SNum, acc)
          val updatedArrObj = newArray(NReal, List(), Some(summaryVal), oldArrayObj, true)

          if (isStrong)
            acc.putObjStrong(arrayAddr, updatedArrObj)
          else   
            acc.putObjWeak(arrayAddr, updatedArrObj)
        }
      }    
      val pushedς = makeState(Num.inject(NReal), x, ρ, σ1, ß, κ, τ)

      pushedς ++ errς
    }
  ), Map("length" → Num.inject(Num.α(1))))

  val Array_prototype_indexOf_Obj =
    constFunctionObj(Sig(NoConversion, List(NoConversion, NumberHint), 1), Num.inject(NReal))
  val Array_prototype_lastIndexOf_Obj =
    constFunctionObj(Sig(NoConversion, List(NoConversion, NumberHint), 1), Num.inject(NReal))

  /* concatenate self with all provided arguments,
     treating non-arrays as singletons */
  val Array_prototype_concat_Obj = createInitFunctionObj(
    Native(
      (selfAddr: BValue, argArrayAddr: BValue, x: Var, ρ: Env, σ: Store, ß:Scratchpad, κ: KStack, τ:Trace) ⇒ {
        assert(argArrayAddr.defAddr,
          "Array.prototype.concat: Arguments array refers to non-addresses")
        assert(argArrayAddr.as.size == 1,
          "Array.prototype.concat: Arguments array refers to multiple addresses")
        val argsArray = σ getObj( argArrayAddr.as.head, SNum )

        val argsSummary = selfAddr ⊔ argsArray(SNum).getOrElse(BValue.⊥)
        /* compute summary of new entries by joining all entries of array arguments
           with all non-array arguments */
        val (arrayAddrs, nonArrayAddrs) = argsSummary.as partition {
          a ⇒ σ.getObj(a, Str.⊥).getJSClass == CArray
        }
        val entrySummary = argsSummary.copy(as = nonArrayAddrs) ⊔ lookup(arrayAddrs, SNum, σ)

        /* allocate new array to house summary */
        val (σ1, resaddr_bv) = allocObj(Address.inject(Array_Addr), τ.toAddr, σ, τ)
        assert(resaddr_bv.as.size == 1,
          "Array.prototype.concat: freshly allocated address set should be singleton")
        val resaddr = resaddr_bv.as.head
        val oldArrayObj = σ1 getObj( resaddr, Str.⊥ )

        val resArray = newArray(NReal, List(), Some(entrySummary), oldArrayObj, true)

        makeState(resaddr_bv, x, ρ, σ1.putObj(resaddr, resArray), ß, κ, τ)
      }
    ), Map("length" → Num.inject(Num.α(1))))

  /* returns new array where all entries are a summary value containing the join
     of all of self's entries */
  val Array_prototype_sort_Obj = createInitFunctionObj(
    Native(
      (selfAddr: BValue, argArrayAddr: BValue, x: Var, ρ: Env, σ: Store, ß:Scratchpad, κ: KStack, τ:Trace) ⇒ {
        // we choose to throw a type error if called on a non-array
        /* TODO: if this sort of thing is a common pattern, factor it out
           into a helper */
        /* TODO: additionally, check if we care about anything which has
           non-TypeError behavior, and if so, account for that. */
        val arrayAddrs = selfAddr.as.filter(a ⇒ σ.getObj(a, Str.⊥).getJSClass == CArray)
  
        if (arrayAddrs.size != selfAddr.as.size)
            makeState(typeError, x, ρ, σ, ß, κ, τ)
        else {
          val arrayAddr = arrayAddrs.head

          val selfArray = σ getObj( arrayAddr, SNum )
          val entrySummary = selfArray(SNum) getOrElse Undef.BV

          /* allocate new array to house summary */
          val (σ1, resaddr_bv) = allocObj(Address.inject(Array_Addr), τ.toAddr, σ, τ)
          assert(resaddr_bv.as.size == 1,
            "Array.prototype.sort: freshly allocated address set should be singleton")
          val resaddr = resaddr_bv.as.head
          val freshObj = σ1 getObj( resaddr, Str.⊥ )

          val resArray = newArray(NReal, List(), Some(entrySummary), freshObj, true)

          makeState(resaddr_bv, x, ρ, σ1.putObj(resaddr, resArray), ß, κ, τ)
        }
      }
    ), Map("length" → Num.inject(Num.α(1))))
  

  /* splice: concretely, takes a start index, number of items to replace, and replacements therefor,
     then modifies self to perform replacement and returns an array of deleted entries.
     abstractly, return new array with all entries being the join of all of self's,
     and modify self such that all of its entries are a summary of its old entries,
     joined with a summary of all replacement arguments */
  val Array_prototype_splice_Obj = createInitFunctionObj(
    Native(
      (selfAddr: BValue, argArrayAddr: BValue, x: Var, ρ: Env, σ: Store, ß:Scratchpad, κ: KStack, τ:Trace) ⇒ {
        assert(argArrayAddr.defAddr,
          "Array.prototype.concat: Arguments array refers to non-addresses")
        assert(argArrayAddr.as.size == 1,
          "Array.prototype.concat: Arguments array refers to multiple addresses")
        val argArray = σ getObj( argArrayAddr.as.head, Str.⊥ )

        // we choose to throw a type error if called on a non-array
        /* TODO: if this sort of thing is a common pattern, factor it out
           into a helper */
        /* TODO: additionally, check if we care about anything which has
           non-TypeError behavior, and if so, account for that. */
        val arrayAddrs = selfAddr.as.filter(a ⇒ σ.getObj(a, Str.⊥).getJSClass == CArray)
        
        if (arrayAddrs.size != selfAddr.as.size)
            makeState(typeError, x, ρ, σ, ß, κ, τ)
        else {    
          val selfArrayAddr = arrayAddrs.head

          val oldSelf = σ getObj( selfArrayAddr, SNum )
          val oldSummary = oldSelf(SNum) getOrElse Undef.BV
          val newSummary = oldSummary ⊔ argArray(SNum).getOrElse(BValue.⊥)

          /* update self with summary including arguments */
          val newSelf = newArray(NReal, List(), Some(newSummary), oldSelf, true)
          val σ1 = σ.putObj(selfArrayAddr, newSelf)

          /* allocate return array */
          val (σ2, retAddr_bv) = allocObj(Address.inject(Array_Addr), τ.toAddr, σ1, τ)
          assert(retAddr_bv.as.size == 1,
            "Array.prototype.concat: freshly allocated address set should be singleton")
          val retAddr = retAddr_bv.as.head
          val freshObj = σ2 getObj( retAddr, Str.⊥ )
          /* populate return array with summary of original array */
          val retArray = newArray(NReal, List(), Some(oldSummary), freshObj, true)
          val σ3 = σ2.putObj(retAddr, retArray)

          makeState(retAddr_bv, x, ρ, σ3, ß, κ, τ)
        }
      }
    ), Map("length" → Num.inject(Num.α(2))))

  val Array_prototype_every_Obj = unimplemented("Array.prototype.every")

  val Array_prototype_filter_Obj = unimplemented("Array.prototype.filter")

  val Array_prototype_forEach_Obj = unimplemented("Array.prototype.foreach")

  val Array_prototype_map_Obj = unimplemented("Array.prototype.map")

  val Array_prototype_reduce_Obj = unimplemented("Array.prototype.reduce")

  val Array_prototype_reduceRight_Obj = unimplemented("Array.prototype.reduceRight")

  val Array_prototype_reverse_Obj = createInitFunctionObj(Native(
    (selfAddr: BValue, argArrayAddr: BValue, x: Var, ρ: Env, σ: Store, ß:Scratchpad, κ: KStack, τ:Trace) ⇒ {
      // we choose to throw a type error if called on a non-array
      val arrayAddrs = selfAddr.as.collect({case a if σ.getObj(a, Str.⊥).getJSClass == CArray ⇒ a})
      if (arrayAddrs.size != selfAddr.as.size) makeState(typeError, x, ρ, σ, ß, κ, τ)
      else {
        val arrayAddr = arrayAddrs.head
        val oldArrayObj = σ getObj( arrayAddr, SNum )
        val summaryVal = lookup(arrayAddrs, SNum, σ)
        val updatedArrObj = oldArrayObj copy (
          extern = oldArrayObj.extern.copy(
            num = Some(summaryVal),
            exactnum = Map()
            )
          )

        makeState(Addresses.inject(arrayAddrs), x, ρ, σ.putObj(arrayAddr, updatedArrObj), ß, κ, τ)
      }
    }
  ), Map("length" → Num.inject(Num.α(0))))

  val Array_prototype_shift_Obj = createInitFunctionObj(Native(
    (selfAddr: BValue, argArrayAddr: BValue, x: Var, ρ: Env, σ: Store, ß:Scratchpad, κ: KStack, τ:Trace) ⇒ {
        // we choose to throw a type error if called on a non-array
      val arrayAddrs = selfAddr.as.collect({case a if σ.getObj(a, Str.⊥).getJSClass == CArray ⇒ a})
      if (arrayAddrs.size != selfAddr.as.size) makeState(typeError, x, ρ, σ, ß, κ, τ)
      else {
        val arrayAddr = arrayAddrs.head
        val oldArrayObj = σ getObj( arrayAddr, Str.⊥ )
        val summaryVal = lookup(arrayAddrs, SNum, σ)

        val updatedArrObj = newArray(NReal, List(), Some(summaryVal), oldArrayObj, true)  
        makeState(summaryVal, x, ρ, σ.putObj(arrayAddr, updatedArrObj), ß, κ, τ) 
      }
    }
  ), Map("length" → Num.inject(Num.α(0))))

  val Array_prototype_slice_Obj = unimplemented("Array.prototype.slice")

  val Array_prototype_some_Obj = unimplemented("Array.prototype.some")

  val Array_prototype_toLocaleString_Obj = unimplemented("Array.prototype.toLocaleString")

  val Array_prototype_toString_Obj = createInitFunctionObj(Native(
    (selfAddr: BValue, argArrayAddr: BValue, x: Var, ρ: Env, σ: Store, ß:Scratchpad, κ: KStack, τ:Trace) ⇒ {
      // ECMA spec
      // 1. Let array be the result of calling ToObject on the this value.
      // 2. Let func be the result of calling the [[Get]] internal method of array with argument "join".
      // 3. If IsCallable(func) is false, then let func be the standard built-in method Object.prototype.toString (15.2.4.2).
      // 4. Return the result of calling the [[Call]] internal method of func providing array as the this value and an empty arguments list.
      val func = lookup(selfAddr.as, Str.α("join"), σ)
      val callableAddrs = func.as.filter(a ⇒ σ.getObj(a, Str.⊥).getCode.nonEmpty) - Array_prototype_toString_Addr
      
      applyClo(Addresses.inject(callableAddrs), selfAddr, Address.inject(Dummy_Arguments_Addr), x, ρ, σ, ß, κ, τ) ++
      (if (!func.defAddr || (callableAddrs.size != func.as.size)) // possible non-function "join"s
        applyClo(Address.inject(Object_prototype_toString_Addr), selfAddr, Address.inject(Dummy_Arguments_Addr), x, ρ, σ, ß, κ, τ)
       else Set()
      )    
    }
  ), Map("length" → Num.inject(Num.α(0))))

  val Array_prototype_unshift_Obj = unimplemented("Array.prototype.unshift")

}
