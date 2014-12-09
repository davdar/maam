// notJS initial state: Function

package notjs.abstracted.init

import notjs.syntax._
import notjs.abstracted.domains._
import notjs.abstracted.domains.AddressSpace._
import notjs.abstracted.helpers.Fields
import notjs.abstracted.helpers.Helpers._
import notjs.abstracted.helpers.Errors
import notjs.abstracted.traces.Trace
import notjs.abstracted.init.Init._
import notjs.abstracted.init.InitHelpers._
import notjs.abstracted.init.StringHelpers._


object InitFunction {

  // creating the object explicitly because the prototype needs to be Object
  val Function_prototype_Obj = createInitObj(
    fields = Map(
      "length" → Num.inject(Num.α(0)),
      "apply" → Address.inject(Function_prototype_apply_Addr), // TODO
      "call" → Address.inject(Function_prototype_call_Addr), // TODO
      "toString" → Address.inject(Function_prototype_toString_Addr) // TODO
    ) ++ dangleMap(Map(
      "constructor" → Address.inject(Function_Addr))),
    internal = Map(
      Fields.proto → Address.inject(Object_prototype_Addr),
      Fields.classname → CFunction_prototype_Obj,
      Fields.code → Set(Native(
        (selfAddr: BValue, argArrayAddr: BValue, x: Var, ρ: Env, σ: Store, ß:Scratchpad, κ: KStack, τ:Trace) ⇒ {
          // TODO: if used as a constructor, throw a type error
          makeState(Undef.BV, x, ρ, σ, ß, κ, τ)
        }))
    )
  )

  val Function_prototype_toString_Obj = constFunctionObj(ezSig(NoConversion, List()), Str.inject(Str.FunctionStr))
 
  val Function_prototype_apply_Obj = createInitFunctionObj(Native(
    (selfAddr: BValue, argArrayAddr: BValue, x: Var, ρ: Env, σ: Store, ß:Scratchpad, κ: KStack, τ:Trace) ⇒ {

      assert(argArrayAddr.defAddr && argArrayAddr.as.size == 1, "Arguments array refers to non-addresses or multiple addresses") 
      val argsObj = σ.getObj(argArrayAddr.as.head)

      val argLength = argsObj(Str.α("length")).getOrElse(BValue.⊥).n
      assert(argLength != Num.⊥, "Arguments length is not a number!")

      // First, cast the first argument to object
      val input = argsObj(Str.α("0")).getOrElse(Undef.BV)
      val traceAddr = τ.toAddr

      val (bv1, σ1, _) = toObjBody(input, σ, τ, traceAddr)

      val (σ2, bv2) = if (input.nil == MaybeNull || input.undef == MaybeUndef) {
         allocObj(Address.inject(Object_Addr), traceAddr, σ1, τ)
      } else (σ1, BValue.⊥)
      
      val newThisAddr = bv2 ⊔ bv1
      
      val extractedArgLength: Option[Int] = argLength match {
        case NConst(d) ⇒ Some(d.toInt)
        case _ ⇒ None
      }


      val intern = Map[Str,Any](Fields.proto → Address.inject(Object_prototype_Addr), Fields.classname → CArguments)
      val tmpArgsObj = Object(ExternMap(), intern, Set())
      extractedArgLength match { // number of arguments passed to .apply
        case Some(2) ⇒ {
          // construct the new arguments object
          val newArgHolderAs_ = argsObj(Str.α("1")).get
          // apply is a typeError if the second arg is not an object
          val mightError = !newArgHolderAs_.defAddr || !selfAddr.defAddr 
          val newArgHolderAs = newArgHolderAs_.as

          val newArgLength = lookup(newArgHolderAs, Str.α("length"), σ2).n
        
          if(newArgLength != Num.⊥) { //, "Apply arguments length is not a number!")

            val newExtractedArgLength: Option[Int] = newArgLength match {
              case NConst(d) ⇒ Some(d.toInt)
              case _ ⇒ None
            }
        
            val newArgsAddr = τ.modAddr(traceAddr, CArguments) 


            val newArgsObj = newExtractedArgLength match {
              case Some(newlen) ⇒ { // Known constant length
                newArray(Num.α(newlen), List.range(0, newlen).map(n ⇒ lookup(newArgHolderAs, Str.α(n.toString), σ2)), None, tmpArgsObj, false)
              }
              case None ⇒ { // Unknown length
                newArray(newArgLength, List(), Option(lookup(newArgHolderAs, SNum, σ2)), tmpArgsObj, false)
              }
            }

            val σ3 = σ2.alloc(newArgsAddr, newArgsObj)
            // Finally, apply.
            applyClo(selfAddr, newThisAddr, Address.inject(newArgsAddr), x, ρ, σ3, ß, κ, τ) ++ 
              (if(mightError) makeState(Errors.typeError, x, ρ, σ, ß, κ, τ) else Set())
          } else makeState(Errors.typeError, x, ρ, σ, ß, κ, τ)
        }

        case Some(1) ⇒ {
          // construct the new empty arguments object
            val newArgsAddr = τ.modAddr(traceAddr, CArguments) 

            val newArgsObj = newArray(Num.Zero, List(), None, tmpArgsObj, false)

            val σ3 = σ2.alloc(newArgsAddr, newArgsObj)
            applyClo(selfAddr, newThisAddr, Address.inject(newArgsAddr), x, ρ, σ3, ß, κ, τ)
          } 
        
        case x ⇒ sys.error("!! Not Implemented: .apply with arguments length = " + x)
      }
    }),
    Map(
      "length" → Num.inject(Num.α(2))
  ))

  val Function_prototype_call_Obj = createInitFunctionObj(Native(
    (selfAddr: BValue, argArrayAddr: BValue, x: Var, ρ: Env, σ: Store, ß:Scratchpad, κ: KStack, τ:Trace) ⇒ {
      assert(argArrayAddr.defAddr && argArrayAddr.as.size == 1, "Arguments array refers to non-addresses or multiple addresses")
      val argsObj = σ.getObj(argArrayAddr.as.head)

      val argLength = argsObj(Str.α("length")).getOrElse(BValue.⊥).n
      assert(argLength != Num.⊥, "Arguments length is not a number!")

      // First, cast the first argument to object
      val input = argsObj(Str.α("0")).getOrElse(Undef.BV)
      val traceAddr = τ.toAddr
      
      val (bv1, σ1, _) = toObjBody(input, σ, τ, traceAddr)

      val (σ2, bv2) = if (input.nil == MaybeNull || input.undef == MaybeUndef) {
         allocObj(Address.inject(Object_Addr), traceAddr, σ1, τ)
      } else (σ1, BValue.⊥)
      
      val newThisAddr = bv2 ⊔ bv1

      val extractedArgLength: Option[Int] = argLength match {
        case NConst(d) ⇒ Some(d.toInt)
        case _ ⇒ None
      }
      
      val newArgsAddr = τ.modAddr(traceAddr, CArguments) // conflicts with newThisAddr, but different class, so it should be ok...
      val intern = Map[Str,Any](Fields.proto → Address.inject(Object_prototype_Addr), Fields.classname → CArguments)
      val tmpArgsObj = Object(ExternMap(), intern, Set())

      // TODO: length 0

      val newArgsObj = extractedArgLength match {
        case Some(newlen) ⇒ { // Known constant length
          newArray(Num.α(newlen-1), List.range(1, newlen).map(n ⇒ argsObj(Str.α(n.toString)).get), None, tmpArgsObj, false)
        }
        case None ⇒ { // Unknown length
          newArray(argLength, List(), argsObj(SNum), tmpArgsObj, false)
        }
      }

    
      val σ3 = σ2.alloc(newArgsAddr, newArgsObj)
      // Finally, call.
      applyClo(selfAddr, newThisAddr, Address.inject(newArgsAddr), x, ρ, σ3, ß, κ, τ) ++
        (if(!selfAddr.defAddr) makeState(Errors.typeError, x, ρ, σ, ß, κ, τ) else Set())
    }
  ), Map("length" → Num.inject(Num.α(1)))
  )
}
