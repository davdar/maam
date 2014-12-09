package notjs.translator

case class BadTransformation(message: String) extends Exception(message)

// -A is the type of the AST we operate on
// -D is the type of information that is passed down
// -U is the type of information that is passed up
trait TransformBase[A, D, U] {
  // Called at the end of transformation.
  // Takes the AST that would have been returned along with the upwards information
  // that would have been returned had it not been called.  By default, this
  // simply passes the information along without modifying it.
  def atTransformEnd(j: A, t: U): (A, U) = (j, t)

  def defaultTransform(p: (A, D)): (A, U) =
    defaultTransform(p._1, p._2)

  def transform(j: A, t: D): (A, U) = 
    transformer.applyOrElse((j -> t), defaultTransform)

  def apply(j: A, t: D): (A, U) = {
    val (fj, ft) = transform(j, t)
    atTransformEnd(fj, ft)
  }

  def apply(j: A): A =
    apply(j, downwardBase)._1

  // BEGIN ABSTRACT MEMBERS

  // Base/seed value for going downward.  Empty sets are often appropriate.
  def downwardBase(): D

  // when you see an AST that matches the given pattern, apply this function
  def transformer: PartialFunction[(A, D), (A, U)]

  // traverses over each member of the given ast, calling transform on it
  def defaultTransform(ast: A, down: D): (A, U)
  // END ABSTRACT MEMBERS
}

// -A is the type of the AST we operate on
// -D is the type of information that is passed down
// -U is the type of information that is passed up
trait TransformPass[A, D, U] extends TransformBase[A, D, U] {
  class TransformMonad[X](val a: X, val ts: List[U]) {
    def flatMap[Y](f: X => (Y, U)): TransformMonad[Y] = {
      val (b, t) = f(a)
      new TransformMonad(b, t :: ts)
    }

    def map[Y](f: X => Y): TransformMonad[Y] =
      new TransformMonad(f(a), ts)
  }

  def addToState(ts: U*): TransformMonad[Unit] =
    new TransformMonad((), ts.toList)

  // I don't know why the compiler isn't always able to apply all the implicits
  implicit def monadToPair[X](m: TransformMonad[X]): (X, U) =
    (m.a, combine(m.ts.reverse))

  implicit def toMonad[X](p: (X, U)): TransformMonad[X] =
    new TransformMonad(p._1, List(p._2))

  implicit def toMonad[X](p: Option[(X, U)]): TransformMonad[Option[X]] =
    new TransformMonad(p.map(_._1), p.map(pp => List(pp._2)).getOrElse(List()))

  // the amount of type hackery needed to remove this duplication is astounding
  implicit def toMonad[X](pairs: Set[(X, U)]): TransformMonad[Set[X]] =
    new TransformMonad(pairs.map(_._1), pairs.map(_._2).toList)

  implicit def toMonad[X](pairs: Seq[(X, U)]): TransformMonad[Seq[X]] =
    new TransformMonad(pairs.map(_._1), pairs.map(_._2).toList)

  implicit def toMonad[X](pairs: List[(X, U)]): TransformMonad[List[X]] =
    new TransformMonad(pairs.map(_._1), pairs.map(_._2).toList)

  // curse you type erasure!
  implicit def optionPairsToMonad[X](pairs: List[Option[(X, U)]]): TransformMonad[List[Option[X]]] =
    new TransformMonad(pairs.map(_.map(_._1)),
                       pairs.flatMap(p => p.map(pp => List(pp._2)).getOrElse(List())))

  def combine(ts: Seq[U]): U =
    ts.foldLeft(upwardBase)(combiner)

  // BEGIN ABSTRACT MEMBERS

  // Base/seed value for going upward.  Empty sets are often appropriate
  def upwardBase(): U

  // Combines two up values into a single value.  For example, with sets, this
  // is often the union operator.
  def combiner(t1: U, t2: U): U
  // END ABSTRACT MEMBERS
}

trait OnlyDownwardPass[A, D] extends TransformPass[A, D, Unit] {
  def upwardBase(): Unit = ()
  def combiner(t1: Unit, t2: Unit): Unit = ()
}

trait OnlyUpwardPass[A, U] extends TransformPass[A, Unit, U] {
  def downwardBase(): Unit = ()
}

// because of type erasure, StatelessTransformPass cannot be defined generically

// Like TransformPass, except the information that is passed up from one call
// is threaded down to the next one.  This needs a whole different monad.
//
// -A is the type of the AST we operate on
// -T is the type of the information that is threaded up and down
trait ThreadedTransformPass[A, T] extends TransformBase[A, T, T] {
  class TransformMonad[X](val needsThread: T => (X, T)) {
    def map[Y](f: X => Y): TransformMonad[Y] =
      new TransformMonad[Y](
        (thread: T) => {
          val (x, t) = needsThread(thread)
          (f(x), t)
        })
    
    def flatMap[Y](f: X => TransformMonad[Y]): TransformMonad[Y] =
      new TransformMonad[Y](
        (thread: T) => {
          val (x, t) = needsThread(thread)
          f(x).needsThread(t)
        })
  }

  implicit def toMonad[X](monads: List[TransformMonad[X]]): TransformMonad[List[X]] =
    new TransformMonad[List[X]](
      (thread: T) => {
        val (finalThread, asts) = monads.foldLeft((thread, List[X]()))((res, cur) => {
          val (curThread, curList) = res
          val (newAst, newThread) = cur.needsThread(curThread)
          (newThread, newAst :: curList)
        })
        (asts.reverse, finalThread)
      })

  implicit def toMonad[X](p: Option[TransformMonad[X]]): TransformMonad[Option[X]] =
    new TransformMonad[Option[X]](
      (thread: T) => 
        p match {
          case Some(m) => {
            val (x, tp) = m.needsThread(thread)
            (Some(x), tp)
          }
          case None =>
           (None, thread)
        })

  implicit def listOptionToMonad[X](list: List[Option[TransformMonad[X]]]): TransformMonad[List[Option[X]]] =
    new TransformMonad[List[Option[X]]](
      (thread: T) => {
        val (finalThread, result) = 
          list.foldLeft((thread, List[Option[X]]()))((res, cur) => {
            val (curThread, accum) = res
            cur match {
              case Some(m) => {
                val (x, tp) = m.needsThread(curThread)
                (tp, Some(x) :: accum)
              }
              case None =>
                (curThread, None :: accum)
            }
          })
        (result.reverse, finalThread)
      })
}
