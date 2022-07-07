module Data.Functor.Sum

import Data.Contravariant

public export
data Sum : (Type -> Type) -> (Type -> Type) -> Type -> Type where
  InL : (f a) -> Sum f g a
  InR : (g a) -> Sum f g a

export
implementation (Functor f, Functor g) => Functor (Sum f g) where
  map f (InL fa) = InL $ f <$> fa
  map f (InR ga) = InR $ f <$> ga

export
implementation (Foldable f, Foldable g) => Foldable (Sum f g) where
  foldr f z (InL fa) = foldr f z fa
  foldr f z (InR ga) = foldr f z ga

export
implementation (Traversable f, Traversable g) => Traversable (Sum f g) where
  traverse f (InL fa) = InL <$> traverse f fa
  traverse f (InR ga) = InR <$> traverse f ga

export
implementation (Contravariant f, Contravariant g) => Contravariant (Sum f g) where
  contramap f (InL fa) = InL $ contramap f fa
  contramap f (InR ga) = InR $ contramap f ga
