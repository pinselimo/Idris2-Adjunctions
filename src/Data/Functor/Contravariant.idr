module Data.Functor.Contravariant

import Data.Contravariant

public export
record Predicate a where
  constructor MkPredicate
  getPredicate : a -> Bool

export
implementation Semigroup (Predicate a) where
  (MkPredicate p) <+> (MkPredicate p') = MkPredicate $ \x => p x && p' x

export
implementation Monoid (Predicate a) where
  neutral = MkPredicate $ \_ => True

export
implementation Contravariant Predicate where
  contramap f (MkPredicate g) = MkPredicate $ g . f
