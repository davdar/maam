# The Problem

The |Monad| class in Haskell:

    class Monad m where
      return ∷ ∀ a. m a
      bind ∷ ∀ a b. m a → (a → m b) → m b

Sets are monads morally, but the |Ord| constraint prevents them from becoming
monads in Haskell. The operations for |Set| are:

    return ∷ ∀ a. (Ord a) ⇒ Set a
    bind ∷ ∀ a b. (Ord a, Ord b) ⇒ Set a → (a → Set b) → Set b

# Non-solution 1

Pin the forall-quantified types into the class, thus splitting |Monad| into two
classes: |Return| and |Bind|.

    class Return m a where
      return ∷ m a

    class Bind m a b where
      bind ∷ m a → (a → m b) → m b

Now you can make instances for |Return Set| and |Bind Set|:

    instance (Ord a) ⇒ Return Set a where ...
    instance (Ord a, Ord b) ⇒ Bind Set a b where ...

This works fine if all you want to do is make a few more things typecheck with
|return| and |bind|.

|-# Limitations

When you start defining monad transformers, things get tricky.

The monad transformer |Trans| class looks like this:

    type m₁ ↝ m₂ = ∀ a. m₁ a → m₂ a
    class Trans t where
      lift ∷ ∀ m. (Monad m) ⇒ m ↝ t m

How would you define |Trans| given |Return| and |Bind|?

    class Trans t where
      liftReturn ∷ ∀ m a. (Return m a, Bind m a ?) ⇒ m a → t m a

In general, instances for Trans will exploit the fact that |a| is universally
quantified, so these instances will need to make even more assumptions about
which types for |a| will satisfy |Monad m a|.

# Non-solution 2

Generalize over an arbitrary constraint:

    class CMonad c m where
      return ∷ (c a) ⇒ a → m a
      bind ∷ (c a, c b) ⇒ m a → (a → m b) → m b

Now you can make an instance for |CMonad Set|:

    instance CMonad Ord Set where

This also works fine if all you want to do is make a few more things typecheck
with |return| and |bind|.

It also lets you get at least some mileage out of monad transformer definitions.

You can now also generalize |Trans| for a given constraint |c|.

    type CMorph c m₁ m₂ = ∀ a. (c a) ⇒ m₁ a → m₂ a
    class CTrans c t where
      lift ∷ ∀ m. (CMonad c m) ⇒ CMorph c m (t m)

|-# Limitations

The problem comes when defining |lift| for monads. To turn an arbitrary |m a|
into a |t m a| you generally need to know that |m| is an |Ord| functor.

    class OrdFunctor m where
      liftOrd ∷ ∀ a. (Ord a) ⇒ W (Ord (m a))

This uses the |W| type, named for "witness", which carries a witness of a
particular constraint fact.

    data W (c ∷ Constraint) where
      W ∷ (c) ⇒ W

More generally, you need to express |c| functorality for an arbitrary
constraint |c|.

    class Functorial c m where
      functorial ∷ ∀ a. (c a) ⇒ W (c (m a))

The |CMonad| class now needs to be changed to claim |m| is also functorial in |c|.

    class (Functorial c m) ⇒ CMonad c m where
      return ∷ (c a) ⇒ a → m a
      bind ∷ (c a, c b) ⇒ m a → (a → m b) → m b

Okay, this isn't _so_ bad. I remember things getting worse in other ways when
trying this approach but never wrote them down.

# Non-solution 3 (my favorite)

It's usually possible to define |bind| for types that require a constraint.
Thus, you split |Monad| into |Return| and |Bind| as before but keep them
polymorphic.

    class Return m where
      return ∷ ∀ a. m a

    class Bind m where
      bind ∷ ∀ a b. m a → (a → m b) → m b

For the example of |Set|, you can make it an instance of |Bind| by:

1. existentially quantifying over an |Ord| witness
2. allowing empty sets which don't have an |Ord| witness

The type looks like this:

    data MySet a where
      EmptyMySet ∷ MySet a
      MySet ∷ (Ord a) ⇒ Set a → MySet a

It is possible to make an instance for |Bind MySet| but not |Return MySet|. You
can then use rebindable syntax and get do-notation for elements in |MySet|.
Instead of writing |return| you write |singleton|, and you're only required to
prove that something is |Ord| at these places.

The other advantage is that you can define |Monad|:

    class (Return m, Bind m) ⇒ Monad m where

This allows you to use the same |Bind| class and functions for things that
admit |Return| instances and those that don't.

|-# Limitations

This has the same flaw as Non-solution 1 in that you can't turn |MySetT| into a
monad transformer. I think you might be able to pull this off with Non-solution
2.
