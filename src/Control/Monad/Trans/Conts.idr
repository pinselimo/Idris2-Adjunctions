module Control.Monad.Trans.Conts

import Control.Comonad
import Control.Monad.Identity
import Control.Monad.Trans

public export
record ContsT (r : Type) (w : Type -> Type) (m : Type -> Type) (a : Type) where
  constructor MkContsT
  runContsT : w (a -> m r) -> m r

public export
Cont : Type -> Type -> Type
Cont r = ContsT r Identity Identity

export
cont : ((a -> r) -> r) -> Cont r a
cont f = MkContsT $ \(Id k) => Id $ f $ runIdentity . k

export
runCont : Cont r a -> (a -> r) -> r
runCont (MkContsT k) f = runIdentity $ k $ Id (Id . f)

public export
Conts : Type -> (Type -> Type) -> Type -> Type
Conts r w = ContsT r w Identity

export
conts : Functor w => (w (a -> r) -> r) -> Conts r w a
conts k = MkContsT $ Id . k . map (runIdentity .)

export
runConts : Functor w => Conts r w a -> w (a -> r) -> r
runConts (MkContsT k) = runIdentity . k . map (Id .)

export
implementation Functor w => Functor (ContsT r w m) where
  map f (MkContsT k) = MkContsT $ k . map (. f)

bindConts : Comonad w => ContsT r w m a -> (a -> ContsT r w m b) -> ContsT r w m b
bindConts (MkContsT k) f = MkContsT $ k . extend (\wa, a => runContsT (f a) wa)

export
implementation Comonad w => Applicative (ContsT r w m) where
  pure x = MkContsT $ flip extract x
  af <*> aa = bindConts {r} af $ \fm                   -- do fm <- af
           => bindConts {r} aa $                       --    a  <- aa
              (\x => MkContsT $ flip extract x) . fm     --    pure $ fm a

export
implementation Comonad w => Monad (ContsT r w m) where
  (>>=) = bindConts

export
implementation Comonad w => MonadTrans (ContsT r w) where
  lift m = MkContsT $ extract . map (m >>=)

export
callCC : Comonad w => ((a -> ContsT r w m b) -> ContsT r w m a) -> ContsT r w m a
callCC f = MkContsT $ \wamr => runContsT (f (\a => MkContsT $ \_ => extract wamr a)) wamr

private
callCCs : Comonad w => (w (a -> ContsT r w m b) -> ContsT r w m a) -> ContsT r w m a
callCCs f = MkContsT $ \wamr => ?hole
