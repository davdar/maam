// notJS initial state: Array-like objects

package notjs.concrete.init

import notjs.syntax._
import notjs.concrete.domains._
import notjs.concrete.interpreter.State
import notjs.concrete.helpers.Fields
import notjs.concrete.helpers.Errors._
import notjs.concrete.helpers.Helpers._

import notjs.concrete.init.Init._
import notjs.concrete.init.InitHelpers._


object InitArrays {

  val Array_Obj = makeNativeValueStore(
      (selfAddr: Address, argArrayAddr: Address, σ: Store) ⇒ {
        val args = σ.getObj(argArrayAddr)

        val calledAsConstr = args.intern.getOrElse(Fields.constructor, false).asInstanceOf[Boolean]

        val (σ1, arrayAddr) = if (calledAsConstr) {
          (σ, selfAddr)
        } else {
          // called as a function: first, construct the array object
          allocObj(Array_Addr, σ)
        }

        val arglen = args(Str("length")) match { // Here and elsewhere I'm trusting that arguments.length does not require prototype lookup
          case Some(Num(n)) ⇒ n
          case _ ⇒ sys.error("inconceivable: arguments without numeric length")
        }
        val internal = σ1.getObj(arrayAddr).intern    
          
        if(arglen == 0 || arglen >=2) {
          // External map: length, and then every argument passed to Array()
          val external = (0 until arglen.toInt).foldLeft(Map[Str, BValue](Str("length") → Num(arglen)))(
           (m:Map[Str, BValue],i:Int) ⇒ (m + (Str(i.toString) → (args(Str(i.toString)).getOrElse(Undef) )))
          )
          
          val newObj = createObj(external, internal)
          val newσ = σ1.putObj(arrayAddr, newObj)
          (arrayAddr, newσ)
        }
        else {
          val len = args(Str("0")).getOrElse(Undef)
          len match {
            case Num(n) ⇒ {
              if(n.toInt != n || n<0) (rangeError, σ)
              else {
                val newObj = createObj(Map(Str("length") → Num(n)), internal)
                val newσ = σ1.putObj(arrayAddr, newObj)
                (arrayAddr, newσ)
              }
            }
            case _ ⇒ {
              val newObj = createObj(Map(Str("length") → Num(1), Str("0") → len), internal)
              val newσ = σ1.putObj(arrayAddr, newObj)
              (arrayAddr, newσ)
            }
          }
        }
      },
    Map(
      Str("prototype") → Array_prototype_Addr,
      Str("isArray") → Array_isArray_Addr,
      Str("length") → Num(1)
    ), myclass = CArray_Obj
  )

  val Array_prototype_Obj = createObj(Map(
    Str("constructor") → Array_Addr,
    Str("concat") → Array_prototype_concat_Addr,
    Str("every") → Array_prototype_every_Addr,
    Str("filter") → Array_prototype_filter_Addr,
    Str("forEach") → Array_prototype_forEach_Addr,
    Str("indexOf") → Array_prototype_indexOf_Addr,
    Str("join") → Array_prototype_join_Addr,
    Str("lastIndexOf") → Array_prototype_lastIndexOf_Addr,
    Str("map") → Array_prototype_map_Addr,
    Str("pop") → Array_prototype_pop_Addr,
    Str("push") → Array_prototype_push_Addr,
    Str("reduce") → Array_prototype_reduce_Addr,
    Str("reduceRight") → Array_prototype_reduceRight_Addr,
    Str("reverse") → Array_prototype_reverse_Addr,
    Str("shift") → Array_prototype_shift_Addr,
    Str("slice") → Array_prototype_slice_Addr,
    Str("some") → Array_prototype_some_Addr,
    Str("sort") → Array_prototype_sort_Addr,
    Str("splice") → Array_prototype_splice_Addr,
    Str("toLocaleString") → Array_prototype_toLocaleString_Addr,
    Str("toString") → Array_prototype_toString_Addr,
    Str("unshift") → Array_prototype_unshift_Addr
  ), Map(Fields.classname → CArray_prototype_Obj))

  val Array_isArray_Obj = makeNativeValue(
      (selfAddr: Address, argArrayAddr: Address, σ: Store) ⇒ {
        val args = σ.getObj(argArrayAddr)
        val input = args(Str("0")).getOrElse(Undef)
        
        input match {
          case a:Address ⇒ Bool(σ.getObj(a).getJSClass == CArray)
          case _ ⇒ Bool(false)
        }
      }, Map(Str("length") → Num(1))
    )

  val Array_prototype_concat_Obj = makeNativeValueStore(
    (selfAddr: Address, argArrayAddr: Address, σ: Store) ⇒ {
      val selfObj = σ.getObj(selfAddr)
      val argObj = σ.getObj(argArrayAddr)

      // allocate a new array
      val newArrayAddr = Address()
      // elements of the new array:
      val selfLength = lookup(selfObj, Str("length"), σ) match {
        case Num(n) ⇒ n
        case _ ⇒ sys.error("!! Not implemented: Array.concat on array of non-numeric length")
      }
      val argLength = lookup(argObj, Str("length"), σ) match {
        case Num(n) ⇒ n
        case _ ⇒ sys.error("Arguments array does not have a non-numeric length ")
      }

      val selfElems = (0 until selfLength.toInt).foldLeft(List[BValue]())((acc, e) ⇒ {
        acc :+ lookup(selfObj, Str(e.toString), σ) 
      })
      val newArrayElems = (0 until argLength.toInt).foldLeft(selfElems)((acc, e) ⇒ {
        acc ++ (lookup(argObj, Str(e.toString), σ) match {
          case a: Address ⇒ {
            val elemObj = σ.getObj(a)
            if (elemObj.getJSClass == CArray) { // unpack the array
              val elemLength = lookup(elemObj, Str("length"), σ) match {
                case Num(n) ⇒ n.toInt
                case _ ⇒ sys.error("Array with non-numeric length")
              }
              (0 until elemLength).foldLeft(List[BValue]())((acc, e) ⇒ {
                acc :+ lookup(elemObj, Str(e.toString), σ)
              })
            }
            else List(a)
          }
          case x ⇒ List(x)
        })
      })
      val newArrayObj = createObj(List.range(0, newArrayElems.length).map(s ⇒ Str(s.toString)).zip(newArrayElems).toMap ++ Map(Str("length") → Num(newArrayElems.length)),
        Map(Fields.proto → Array_prototype_Addr,
            Fields.classname → CArray))
      val σ1 = σ.putObj(newArrayAddr, newArrayObj)
      (newArrayAddr, σ1)
    }, Map(Str("length") → Num(1)))

  val Array_prototype_every_Obj = unimplemented

  val Array_prototype_filter_Obj = unimplemented

  val Array_prototype_forEach_Obj = unimplemented

  val Array_prototype_indexOf_Obj = approx_num

  val Array_prototype_join_Obj = makeNativeValue(
      (selfAddr: Address, argArrayAddr: Address, σ: Store) ⇒ {
        val args = σ.getObj(argArrayAddr)
        val self = σ.getObj(selfAddr)
        val separator = args(Str("0")) match {
          case Some(Undef) ⇒ Str(",")
          case Some(v) ⇒ ToString(v, σ)
          case None ⇒ Str(",")
        }
        val len = lookup(self, Str("length"), σ) match { // TODO: Should do a toUInt32 on the lookup'd value
          case Num(n) ⇒ n
          case _ ⇒ sys.error("!! Not Implemented: Array.join on array of non-numeric length")
        }
        
        if(len == 0) Str("")
        else {
          val start = lookup(self, Str("0"), σ) match {
            case Null | Undef ⇒ Str("")
            case v ⇒ ToString(v, σ)
          }
          (1 until len.toInt).foldLeft(start)( (s:Str, i:Int) ⇒ s ++ (lookup(self, Str(i.toString), σ) match {
            case Null | Undef ⇒ separator ++ Str("")
            case v ⇒ separator ++ ToString(v, σ)
          }))
        }

      }, Map(Str("length") → Num(1))
  )

  val Array_prototype_lastIndexOf_Obj = approx_num

  val Array_prototype_map_Obj = unimplemented

  val Array_prototype_pop_Obj = makeNativeValueStore(
      (selfAddr: Address, argArrayAddr: Address, σ: Store) ⇒ {
        val self = σ.getObj(selfAddr)
        val len = lookup(self, Str("length"), σ)
        // TODO: Strictly speaking, we need to do some ToUInt32 stuff here.
        // For now, assume len is an integer.
        len match {
          case Num(n) ⇒ {
            // Update length of self to be zero (previously it might have inherited from its parent)
            if(n == 0) (Undef, σ.putObj(selfAddr, self.upd(Str("length"), Num(0))))
            else {
              val last = Str((n.toInt-1).toString)
              val rv = lookup(self, last, σ)
              val (o1, _) = self − last
              (rv, σ.putObj(selfAddr, o1.upd(Str("length"), Num(n-1))))
            }
          }
          case _  ⇒ sys.error("!! Not Implemented: unreasonable length value")
        }
      }, Map(Str("length") → Num(0))
    )

  val Array_prototype_push_Obj = makeNativeValueStore(
      (selfAddr: Address, argArrayAddr: Address, σ: Store) ⇒ {
        val self = σ.getObj(selfAddr)
        val len = lookup(self, Str("length"), σ) match {
          case Num(n) ⇒ n.toInt
          case _ ⇒ sys.error("inconceivable: array without sane length")
        }
        // TODO: Should do some ToUInt32 stuff on len here
        val argsObj = σ.getObj(argArrayAddr)
        val arglen = argsObj(Str("length")) match {
          case Some(Num(n)) ⇒ n.toInt
          case _ ⇒ sys.error("inconceivable: args without length")
        }
        val σ1 = (0 until arglen).foldLeft(σ)( (acc, n) ⇒ acc.putObj(
          selfAddr,
          acc.getObj(selfAddr).upd(Str((n+len).toString), argsObj(Str(n.toString)).get)
        ))
        val σ2 = σ1.putObj(selfAddr, σ1.getObj(selfAddr).upd(Str("length"), Num(arglen + len)))

        (Num(arglen + len), σ2)
      }, Map(Str("length") → Num(1))
    )

  val Array_prototype_reduce_Obj = unimplemented

  val Array_prototype_reduceRight_Obj = unimplemented

  val Array_prototype_reverse_Obj = makeNativeValueStore(
    (selfAddr: Address, argArrayAddr: Address, σ: Store) ⇒ {
      val selfObj = σ.getObj(selfAddr)
      val len = lookup(selfObj, Str("length"), σ) match {
        case Num(n) ⇒ n.toInt
        case _ ⇒ sys.error("inconceivable: array without sane length")
      }
      val curList = List.range(0, len).map(i ⇒ lookup(selfObj, Str(i.toString), σ))
      val reversedList = curList.reverse
      val newσ = List.range(0, len).zip(reversedList).foldLeft(σ)((acc, tup) ⇒ acc.putObj(
        selfAddr, 
        acc.getObj(selfAddr).upd(Str(tup._1.toString), tup._2)
      ))
      (selfAddr, newσ)
    }, Map(Str("length") → Num(0))
  )

  val Array_prototype_shift_Obj = makeNativeValueStore(
    (selfAddr: Address, argArrayAddr: Address, σ: Store) ⇒ {
      val selfObj = σ.getObj(selfAddr)
      val len = lookup(selfObj, Str("length"), σ) match {
        case Num(n) ⇒ n.toInt
        case _ ⇒ sys.error("inconceivable: array without sane length")
      }
      if (len == 0) (Undef, σ) // TODO: make this same as pop?
      else {
        val first = lookup(selfObj, Str("0"), σ)
        val last = Str((len-1).toString)
        val newList = List.range(1, len).map(i ⇒ lookup(selfObj, Str(i.toString), σ))
        
        val σ1 = List.range(0, len-1).zip(newList).foldLeft(σ)((acc, tup) ⇒ acc.putObj(
          selfAddr, 
          acc.getObj(selfAddr).upd(Str(tup._1.toString), tup._2)
        ))
        val (o1, _) = σ1.getObj(selfAddr) − last
        val σ2 = σ1.putObj(selfAddr, o1.upd(Str("length"), Num(len-1)))
        (first, σ2)
      }
    }, Map(Str("length") → Num(0))
  )

  val Array_prototype_slice_Obj = unimplemented

  val Array_prototype_some_Obj = unimplemented

  val Array_prototype_sort_Obj = unimplemented

  val Array_prototype_splice_Obj = unimplemented

  val Array_prototype_toLocaleString_Obj = unimplemented

  // 'The result of calling this function is the same as if the built-in join method were invoked for this object with no argument.'
  // TODO: factor out commonality
  // Except, unlike .join, this is _not_ generic.
  val Array_prototype_toString_Obj = makeNativeValue(
      (selfAddr: Address, argArrayAddr: Address, σ: Store) ⇒ {
        val self = σ.getObj(selfAddr)
        self.getJSClass match {
          case CArray ⇒ {
            val separator = Str(",")
            val len = lookup(self, Str("length"), σ) match { // TODO: Should do a toUInt32 on the lookup'd value
              case Num(n) ⇒ n
              case _ ⇒ sys.error("!! Not Implemented")
            }
            
            if(len == 0) Str("")
            else {
              val start = lookup(self, Str("0"), σ) match { // TODO: Should have ToString() here
                case Null | Undef ⇒ Str("")
                case v ⇒ ToString(v, σ)
              }
              (1 until len.toInt).foldLeft(start)( (s:Str, i:Int) ⇒ s ++ (lookup(self, Str(i.toString), σ) match {
                case Null | Undef ⇒ separator ++ Str("")
                case v ⇒ separator ++ ToString(v, σ)
              }))
            }
          }
          case _ ⇒ typeError
        }
      }, Map(Str("length") → Num(0))
    )

  val Array_prototype_unshift_Obj = unimplemented

}
