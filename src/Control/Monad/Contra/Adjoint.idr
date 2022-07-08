module Control.Monad.Contra.Adjoint

import Control.Comonad
import Control.Monad.Identity
import Data.Contravariant

import Data.Functor.Contravariant.Adjunction

public export
record AdjointT (f : Type -> Type) (g : Type -> Type) (w : Type -> Type) (a : Type) where
  constructor AdjoinT
  runAdjointT : g (w (f a))

public export
Adjoint : (Type -> Type) -> (Type -> Type) -> Type -> Type
Adjoint f g = AdjointT f g Identity

export
adjoint : Contravariant g => g (f a) -> Adjoint f g a
adjoint = AdjoinT . contramap runIdentity

export
runAdjoint : Contravariant g => Adjoint f g a -> g (f a)
runAdjoint = contramap Id . runAdjointT

export
implementation (Adjunction f g r, Functor w) => Functor (AdjointT f g w) where
  map f (AdjoinT g) = AdjoinT $ contramap (map (contramap f)) g

private
bindAdjoint : (Adjunction f g r, Comonad w) => AdjointT f g w a -> (a -> AdjointT f g w b) -> AdjointT f g w b
bindAdjoint (AdjoinT m) f = AdjoinT $ contramap (extend (rightAdjunct {r=r} (runAdjointT . f))) m

export
implementation (Adjunction f g r, Comonad w) => Applicative (AdjointT f g w) where
  pure = AdjoinT . leftAdjunct {f=f, r=r} extract
  af <*> aa = bindAdjoint {r} af $ \fm                   -- do fm <- af
           => bindAdjoint {r} aa $                          -- a  <- aa
              AdjoinT . leftAdjunct {f=f, r=r} extract . fm -- pure $ fm a

export
implementation (Adjunction f g r, Comonad w) => Monad (AdjointT f g w) where
  (>>=) = bindAdjoint {r}
  join x = bindAdjoint {r} x id

