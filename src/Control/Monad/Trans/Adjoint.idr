module Control.Monad.Trans.Adjoint

import Control.Monad.Identity
import Control.Monad.Trans

import Data.Distributive
import Data.Functor.Adjunction
import Data.Functor.Rep

public export
record AdjointT (f : Type -> Type) (g : Type -> Type) (m : Type -> Type) (a : Type) where
  constructor AdjoinT
  runAdjointT : g (m (f a))

public export
Adjoint : (Type -> Type) -> (Type -> Type) -> Type -> Type
Adjoint f g = AdjointT f g Identity

export
adjoint : Functor g => g (f a) -> Adjoint f g a
adjoint = AdjoinT . map Id

export
runAdjoint : Functor g => Adjoint f g a -> g (f a)
runAdjoint = map runIdentity . runAdjointT

export
implementation (Adjunction f g r, Monad m) => Functor (AdjointT f g m) where
  map f (AdjoinT g) = AdjoinT $ map (map (map f)) g

bindAdjoint : (Adjunction f g r, Monad m) => AdjointT f g m a -> (a -> AdjointT f g m b) -> AdjointT f g m b
bindAdjoint (AdjoinT m) f = AdjoinT $ map (>>= rightAdjunct {r} (runAdjointT . f)) m

export
implementation (Adjunction f g r, Monad m) => Applicative (AdjointT f g m) where
  pure = AdjoinT . leftAdjunct {f, r} pure
  af <*> aa = bindAdjoint {r} af $ \fm                   -- do fm <- af
           => bindAdjoint {r} aa $                       --    a  <- aa
              AdjoinT . leftAdjunct {f, r} pure . fm     --    pure $ fm a

export
implementation (Adjunction f g r, Monad m) => Monad (AdjointT f g m) where
  (>>=) = bindAdjoint {r}
  join x = bindAdjoint {r} x id

export
implementation (Adjunction f g r, Traversable f) => MonadTrans (AdjointT f g) where
  lift = AdjoinT . map sequence . unit {f, r}

