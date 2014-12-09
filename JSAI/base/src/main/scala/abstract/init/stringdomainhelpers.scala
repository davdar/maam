// Those helpers requiring modification per custom string domain.

package notjs.abstracted.init

import notjs.syntax._
import notjs.abstracted.domains._
import notjs.abstracted.domains.AddressSpace._
import notjs.abstracted.traces.Trace
import notjs.abstracted.helpers.Helpers._
import notjs.abstracted.helpers.Errors._
import notjs.abstracted.helpers.Fields
import notjs.abstracted.interpreter.State
import notjs.abstracted.interpreter.notJS
import notjs.abstracted.init.Init._

object StringHelpers {

  /* Used for creating initial objects: builds the proper ExternMap and present set and so on. */
  def createInitObjCore(fields: Map[String, BValue], internal: Map[Str, Any]): Object = {
    val exactnotnum = fields.keys.filterNot(Str.isNum).foldLeft(Map[Str, BValue]())((acc, field) ⇒ acc ++ Map(Str.α(field) → fields(field)))

    val exactnum = fields.keys.filter(Str.isNum).foldLeft(Map[Str, BValue]())((acc, field) ⇒ acc ++ Map(Str.α(field) → fields(field)))

    val external = ExternMap(exactnotnum = exactnotnum, exactnum = exactnum)

    Object(external, internal, exactnotnum.keys.toSet)
  }




  /* Helper for creating and updating arrays. If update is true, this method copies
  origArray's properties to the Object returned, excepting the numeric and length properties.
  Otherwise, it copies only the internal properties (prototype and so on).
  Arguments objects are basically array objects, except with a different class and prototype;
  they can also be created with this method by passing in an Arguments object instead of an Array object.
  TODO: factor this into an update and non-update version.
  */
  def newArray(length: Num, exactEntries: List[BValue] = List(), summaryVal: Option[BValue], origArray: Object, update: Boolean): Object = {
      val exactnum = exactEntries.zipWithIndex.foldLeft(Map[Str, BValue]()) ((acc, t) ⇒ acc + (t match {case (v, index) ⇒ {
          (Str.α(index.toString) → v)
        }}))

      if(update) {
        val exactnotnum = origArray.extern.exactnotnum + (Str.α("length") → Num.inject(length))
        Object(
          ExternMap(
            top = origArray.extern.top,
            notnum = origArray.extern.notnum,
            num = summaryVal,
            exactnotnum = exactnotnum,
            exactnum = exactnum
          ),
          origArray.intern,
          (exactnotnum.keys ++ exactnum.keys).toSet
        )

      }
      else {
        val exactnotnum = Map[Str, BValue](Str.α("length") → Num.inject(length))
        Object(
          ExternMap(
            num = summaryVal,
            exactnotnum = exactnotnum,
            exactnum = exactnum
          ),
          origArray.intern,
          (exactnotnum.keys ++ exactnum.keys).toSet
        )
      }
  }

  /* Helper for making a new ArrayBuffer object. */
  def newArrayBuffer(length_bv: BValue, oldObj: Object): Object =
    Object(extern = ExternMap(num = Some(Num.inject(Num.Zero) ⊔ Undef.BV),
      exactnotnum = Map(Str.α("byteLength") → length_bv)),
      intern = oldObj.intern, present = oldObj.present + Str.α("byteLength"))

  

}