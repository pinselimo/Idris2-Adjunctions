module Control.Comonad.Contra.Adjoint

import Control.Comonad
import Control.Monad.Identity
import Data.Contravariant

import Data.Functor.Contravariant.DualAdjunction

public export
record AdjointT (0 f : Type -> Type) (0 g : Type -> Type) (0 m : Type -> Type) a where
  constructor AdjoinT
  runAdjointT : f (m (g a))

public export
Adjoint : (Type -> Type) -> (Type -> Type) -> Type -> Type
Adjoint f g = AdjointT f g Identity

export
adjoint : Contravariant f => f (g a) -> Adjoint f g a
adjoint = AdjoinT . contramap runIdentity

export
runAdjoint : Contravariant f => Adjoint f g a -> f (g a)
runAdjoint = contramap Id . runAdjointT

export
implementation (Contravariant f, Contravariant g, Monad m) => Functor (AdjointT f g m) where
  map f (AdjoinT g) = AdjoinT $ contramap (map (contramap f)) g

export
implementation (DualAdjunction f g, Monad m) => Comonad (AdjointT f g m) where
  extract = rightAdjunctOp pure . runAdjointT
  extend f = AdjoinT . contramap (>>= leftAdjunctOp (f . AdjoinT)) . runAdjointT
