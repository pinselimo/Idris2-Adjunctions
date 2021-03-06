module Data.Functor.Contravariant.Adjunction

import Data.Contravariant
import Data.Morphisms
import Data.Profunctor

import Data.Functor.Contravariant
import Data.Functor.Contravariant.Rep

public export
interface (Contravariant f, Contravariant g, Representable g r) => Adjunction f g r where
  unit : a -> g (f a)
  unit = leftAdjunct {g, r} id
  counit : a -> f (g a)
  counit = rightAdjunct {r} id
  leftAdjunct : (b -> f a) -> a -> g b
  leftAdjunct f = contramap f . unit {g, r}
  rightAdjunct : (a -> g b) -> b -> f a
  rightAdjunct f = contramap f . counit {r}

export
adjuncted : (Adjunction f g r, Profunctor p, Functor h)
         => p (a -> g b) (h (c -> g d)) -> p (b -> f a) (h (d -> f c))
adjuncted = dimap (leftAdjunct {r}) (map (rightAdjunct {r}))

export
contrarepAdjunction : Adjunction f g r => (a -> f ()) -> g a
contrarepAdjunction = flip (leftAdjunct {r}) ()

export
coindexAdjunction : Adjunction f g r => g a -> a -> f ()
coindexAdjunction = (rightAdjunct {r}) . const

export
implementation Adjunction Predicate Predicate Bool where
  unit a = MkPredicate (\k => k.getPredicate a)
  counit = unit {f=Predicate, g=Predicate, r=Bool}
