module Data.Functor.Product

import Data.Contravariant

public export
record Product (f : Type -> Type) (g : Type -> Type) (a : Type) where
  constructor Pair
  fst : f a
  snd : g a

export
implementation (Functor f, Functor g) => Functor (Product f g) where
  map h (Pair f g) = Pair (map h f) (map h g)

export
implementation (Applicative f, Applicative g) => Applicative (Product f g) where
  pure x = Pair (pure x) (pure x)
  Pair f g <*> Pair f' g' = Pair (f <*> f') (g <*> g')

export
implementation (Monad f, Monad g) => Monad (Product f g) where
  Pair m n >>= h = Pair (m >>= fstP . h) (n >>= sndP . h)
    where fstP : Product f g x -> f x
          fstP (Pair f _) = f
          sndP : Product f g x -> g x
          sndP (Pair _ g) = g

export
implementation (Foldable f, Foldable g) => Foldable (Product f g) where
  foldr fu z (Pair f g) = foldr fu (foldr fu z g) f

export
implementation (Traversable f, Traversable g) => Traversable (Product f g) where
  traverse fu (Pair f g) = Pair <$> traverse fu f <*> traverse fu g

export
implementation (Alternative f, Alternative g) => Alternative (Product f g) where
  empty = Pair empty empty
  Pair f g <|> Pair f' g' = Pair (f <|> f') (g <|> g')

export
implementation (Contravariant f, Contravariant g) => Contravariant (Product f g) where
  contramap c (Pair f g) = Pair (contramap c f) (contramap c g)

