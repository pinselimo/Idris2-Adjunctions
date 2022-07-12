module Control.Comonad.Trans.Adjoint

import Control.Comonad
import Control.Comonad.Trans
import Control.Monad.Identity

import Data.Distributive
import Data.Functor.Adjunction

public export
record AdjointT (f : Type -> Type) (g : Type -> Type) (w : Type -> Type) a where
  constructor AdjoinT
  runAdjointT : f (w (g a))

public export
Adjoint : (Type -> Type) -> (Type -> Type) -> Type -> Type
Adjoint f g = AdjointT f g Identity

export
adjoint : Functor f => f (g a) -> Adjoint f g a
adjoint = AdjoinT . map Id

export
runAdjoint : Functor f => Adjoint f g a -> f (g a)
runAdjoint = map runIdentity . runAdjointT

export
implementation (Functor f, Functor g, Functor w) => Functor (AdjointT f g w) where
  map f (AdjoinT g) = AdjoinT $ map (map (map f)) g

export
implementation (Adjunction f g r, Comonad w) => Comonad (AdjointT f g w) where
  extend l (AdjoinT m) = AdjoinT $ map (extend $ leftAdjunct {f, r} (l . AdjoinT)) m
  extract = rightAdjunct {r} extract . runAdjointT
  duplicate (AdjoinT m) = AdjoinT $ map (extend $ leftAdjunct {f, r} (id . AdjoinT)) m

export
implementation (Distributive f, Adjunction f g r, Applicative m, Comonad m) => Applicative (AdjointT f g m) where
  pure = AdjoinT . map pure . distribute . unit {f, r}
  AdjoinT ff <*> AdjoinT fa = AdjoinT $ map (map $ rightAdjunct {r} extract ff) <$> fa

export
implementation (Adjunction f g r, Distributive g) => ComonadTrans (AdjointT f g) where
  lower = counit {r} . map distribute . runAdjointT
