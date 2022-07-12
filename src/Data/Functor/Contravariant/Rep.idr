module Data.Functor.Contravariant.Rep

import Data.Contravariant
import Data.Morphisms
import Data.Profunctor

import Data.Functor.Contravariant
import Data.Functor.Product

public export
interface Contravariant f => Representable (0 f : Type -> Type) (0 g : Type) where
  tabulate : (a -> g) -> f a
  index : f a -> a -> g

  contramapWithRep : (b -> Either a g) -> f a -> f b
  contramapWithRep f p = tabulate $ either (index p) id . f

%inline
export
tabulated : (Representable f a, Representable g b, Profunctor p, Functor h)
         => p (f a) (h (g b)) -> p (a -> a) (h (b -> b))
tabulated = dimap tabulate (map index)

export
contramapRep : Representable f x => (a -> b) -> f b -> f a
contramapRep g = tabulate {f, g=x} . (. g) . index

export
implementation Representable (Op r) r where
  tabulate = MkOp
  index = applyOp

export
implementation Representable Predicate Bool where
  tabulate = MkPredicate
  index = getPredicate

export
implementation (Representable f a, Representable g b, Functor f)
  => Representable (Product f g) (Pair a b) where
  tabulate f = Pair (tabulate (fst . f)) (tabulate (snd . f))
  index (Pair f g) a = (index f a, index g a)
  contramapWithRep h (Pair f g) = Pair
    (contramapWithRep (map fst . h) f)
    (contramapWithRep (map snd . h) g)

