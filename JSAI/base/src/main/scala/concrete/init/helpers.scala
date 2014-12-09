// Helpers for initial notJS state

package notjs.concrete.init

import notjs.syntax._
import notjs.concrete.domains._
import notjs.concrete.interpreter.State
import notjs.concrete.helpers.Fields
import notjs.concrete.helpers.Errors._
import notjs.concrete.helpers.Helpers._

import notjs.concrete.init.Init._


object InitHelpers {

    // stub for unimplemented concrete functions
    val unimplemented = createFunctionObj(Native(
        (selfAddr: Address, argArrayAddr: Address, x: Var, ρ: Env, σ: Store, ß:Scratchpad, κ: KStack) ⇒
          sys.error("!! Not Implemented")
      ), Map(Str("length") → Num(0))
    )
    
    // The following three function objects are for concrete functions which are not yet implemented, just so we can be sure we're over-approximating
    val approx_str = makeNativeValue(
      (selfAddr: Address, argArrayAddr: Address, σ: Store) ⇒ {
        println("warning: use of approximated concrete function")
        Str("UNIMPLEMENTED")
      }, Map(Str("length") → Num(1)) // Not necessarily correct! But it should be alright since real-world code rarely inspects this, and this is an approximation anyway
    )

    val approx_num = makeNativeValue(
      (selfAddr: Address, argArrayAddr: Address, σ: Store) ⇒ {
        println("warning: use of approximated concrete function")
        Num(0)
      }, Map(Str("length") → Num(1)) // Not necessarily correct! But it should be alright since real-world code rarely inspects this, and this is an approximation anyway
    )
    
    val approx_array = makeNativeValueStore(
      (selfAddr: Address, argArrayAddr: Address, σ: Store) ⇒ {
        println("warning: use of approximated concrete function")
        val (σ1, arrayAddr) = allocObj(Array_Addr, σ)
        val internal = σ1.getObj(arrayAddr).intern
        val newObj = createObj(Map(Str("length") → Num(1), Str("0") → Str("UNIMPLEMENTED ARRAY")), internal)
        val newσ = σ1.putObj(arrayAddr, newObj)
        (arrayAddr, newσ)
      }, Map(Str("length") → Num(1))
    )




    // A couple of places need this conversion.
    def JSClassToString(j: JSClass): String = { 
    // TODO: remaining classes
      j match {
        case CObject ⇒ "Object"
        case CFunction ⇒ "Function"
        case CArray ⇒ "Array"
        case CString ⇒ "String"
        case CBoolean ⇒ "Boolean"
        case CNumber ⇒ "Number"
        case CDate ⇒ "Date"
        case CError ⇒ "Error"
        case CRegexp ⇒ "Regexp"
        case CArguments ⇒ "Arguments"
        case CObject_Obj ⇒ "Function"
        case CObject_prototype_Obj ⇒ "Object"
        case CArray_prototype_Obj ⇒ "Array"
        case CArray_Obj ⇒ "Function"
        case CFunction_Obj ⇒ "Function"
        case CFunction_prototype_Obj  ⇒ "Function"
        case CMath_Obj ⇒ "Math"
        case CNumber_Obj ⇒ "Function"
        case CNumber_prototype_Obj ⇒ "Number"
        case CString_Obj ⇒ "Function"
        case CString_prototype_Obj ⇒ "String"
      }
    }

    def Object_toString_helper(o: Object): Str =
      Str("[object " + JSClassToString(o.getJSClass) + "]")
  
    
    // Type conversion. TODO: Only handles the trivial cases.
    def ToNumber(v: BValue, σ: Store): Num =
      v match {
        case a:Address ⇒ {
          val o = σ getObj a
          val valueOf = lookup(o, Str("valueOf"), σ)
    
          val value = valueOf match {
            case _ if(valueOf == Number_prototype_valueOf_Addr) ⇒ o.getValue.get
            case _ if(valueOf == String_prototype_valueOf_Addr) ⇒ o.getValue.get
            case _ if(valueOf == Boolean_prototype_valueOf_Addr) ⇒ o.getValue.get
            case _ ⇒ sys.error("Your valueOf is not sane.")
          }
          ToNumber(value, σ)
        }
        case _ ⇒ v.tonum
      }
    
    def ToString(v: BValue, σ: Store): Str = // TODO: this only handles easy cases
      v match {
        case a:Address ⇒ {
          val o = σ getObj a
          val toString = lookup(o, Str("toString"), σ)
          
          val string = toString match {
            case _ if(toString == Number_prototype_toString_Addr) ⇒ o.getValue.get.tostr
            case _ if(toString == String_prototype_toString_Addr) ⇒ o.getValue.get
            case _ if(toString == Boolean_prototype_toString_Addr) ⇒ o.getValue.get.tostr
            case _ if(toString == Object_prototype_toString_Addr) ⇒ Object_toString_helper(o)
            case _ if(toString == Array_prototype_toString_Addr) ⇒ ArrayToString(a, σ)
            case _ ⇒ sys.error("Your toString is not sane.")
          }
          ToString(string, σ)
        }
        case _ ⇒ v.tostr
      }

    def ArrayToString(a: Address, σ: Store): Str = {
      val arrayObj = σ.getObj(a)
      val separator = Str(",")
      val len = lookup(arrayObj, Str("length"), σ) match { // TODO: Should do a toUInt32 on the lookup'd value
        case Num(n) ⇒ n.toInt
        case _ ⇒ sys.error("!! Non-numeric array length not handled")
      }
      
      if(len == 0) Str("")
      else {
        val start = lookup(arrayObj, Str("0"), σ) match { // TODO: Should have ToString() here
          case Null | Undef ⇒ Str("")
          case v ⇒ ToString(v, σ)
        }
        (1 until len.toInt).foldLeft(start)( (s:Str, i:Int) ⇒ s ++ (lookup(arrayObj, Str(i.toString), σ) match {
          case Null | Undef ⇒ separator ++ Str("")
          case v ⇒ separator ++ ToString(v, σ)
        }))
      }
    } 
      
    // the Value returned will either be an address or a typeError
    def ToObject(v: BValue, σ: Store): (Value, Store) = { // JavaScript type conversion, 262: 9.9
      v match {
        case a:Address ⇒ (a, σ)
        case Null | Undef ⇒ (typeError, σ)
        case _ ⇒ {
          val (proto, classname) = v match {
            case s:Str ⇒ (String_prototype_Addr, CString)
            case b:Bool ⇒ (Boolean_prototype_Addr, CBoolean)
            case n:Num ⇒ (Number_prototype_Addr, CNumber)
            case _ ⇒ sys.error("inconceivable")
          }
          val newAddr = Address()
          val newObj = createObj(Map(), Map(
            Fields.proto → proto,
            Fields.classname → classname,
            Fields.value → v))
          val newσ = σ.putObj(newAddr, newObj)
          (newAddr, newσ)
        }
      }
    }


    // Make objects and ensure they have prototypes and classes.
    def createObj(external: Map[Str, BValue], internal: Map[Str, Any] = Map()): Object = {
      val internalFieldMap = if (!internal.contains(Fields.proto))
        internal ++ Map(Fields.proto → Object_prototype_Addr)
      else
        internal
  
      val internalFieldMap1 = if (!internal.contains(Fields.classname))
        internalFieldMap ++ Map(Fields.classname → CObject)
      else
        internalFieldMap
      
      Object(external, internalFieldMap1)
    }

    // Make function objects and set their prototype, class, and code fields.
    def createFunctionObj(clo: Native, external: Map[Str, BValue], internal: Map[Str, Any] = Map(), myclass: JSClass = CFunction): Object = {
      assert(external contains Str("length"), "Native function with no length.")
      val internalFieldMap = internal ++ Map(Fields.proto → Function_prototype_Addr, Fields.code → clo, Fields.classname → myclass)
      Object(external, internalFieldMap)
    }
    
    
    // Helpers for common Native cases.
    
    // Makes a Native function from a function returning a value and a store
    def makeNativeValueStore(f:(Address, Address, Store) ⇒ (Value, Store),  external: Map[Str, BValue], myclass: JSClass = CFunction): Object = {
      createFunctionObj(Native((selfAddr: Address, argArrayAddr: Address, x: Var, ρ: Env, σ: Store, ß:Scratchpad, κ: KStack) ⇒ {
        val (rv, newσ) = f(selfAddr, argArrayAddr, σ)
        makeState(rv, x, ρ, newσ, ß, κ)
      }), external, myclass = myclass)
    }

    // Makes a Native function from a function returning just a value
    def makeNativeValue(f:(Address, Address, Store) ⇒ Value,  external: Map[Str, BValue]): Object = {
      createFunctionObj(Native((selfAddr: Address, argArrayAddr: Address, x: Var, ρ: Env, σ: Store, ß:Scratchpad, κ: KStack) ⇒ {
        val rv = f(selfAddr, argArrayAddr, σ)
        makeState(rv, x, ρ, σ, ß, κ)
      }), external)
    }
    
    def makeState(v: Value, x: Var, ρ: Env, σ: Store, ß: Scratchpad, κ: KStack): State = {
      v match {
          case bv:BValue ⇒ x match {
            case pv:PVar ⇒ State( bv, ρ, σ + (ρ(pv) → bv), ß, κ)
            case sc:Scratch ⇒ State( bv, ρ, σ, ß.update(sc, bv), κ )
          }
          case _ ⇒ State( v, ρ, σ, ß, κ)
      }
    }


    // helper for mathematical functions, which are often identical to their Scala counterparts
    def makeMath(f:Double ⇒ Double): Object = makeNativeValue(
      (selfAddr: Address, argArrayAddr: Address, σ: Store) ⇒ {
        val argsObj = σ.getObj(argArrayAddr)
        
        val inp = ToNumber(argsObj(Str("0")).getOrElse(Undef), σ).n

        if (inp == Double.NaN) {
          Num(Double.NaN)
        } else {
          Num(f(inp))
        }

      }, Map(Str("length") → Num(1)) 
  )

}
