module Control.Comonad.Representable.Store

import Control.Monad.Identity
import Control.Comonad
import Control.Comonad.Env
import Control.Comonad.Store.Interface
import Control.Comonad.Traced
import Control.Comonad.Trans

import Data.Functor.Rep

public export
record StoreT {r : Type} (g : Type -> Type) (w : Type -> Type) (a : Type) where
  constructor MkStoreT
  run : w (g a)
  val : r

public export
Store : {r : Type} -> (Type -> Type) -> Type -> Type
Store g = StoreT {r} g Identity

export
storeT : (Functor w, Representable g r) => w (r -> a) -> r -> StoreT {r} g w a
storeT f s = MkStoreT (map tabulate f) s

export
runStoreT : (Functor w, Representable g r) => StoreT {r} g w a -> (w (r -> a), r)
runStoreT (MkStoreT w s) = (index <$> w, s)

export
store : Representable g r => (r -> a) -> r -> Store {r} g a
store = storeT . Id

export
runStore : (Functor w, Representable g r) => Store {r} g a -> ((r -> a), r)
runStore (MkStoreT (Id ga) k) = (index ga, k)

export
implementation (Functor w, Functor g) => Functor (StoreT {r} g w) where
  map f (MkStoreT w s) = MkStoreT (map (map f) w) s

export
implementation (Applicative w, Monoid r, Functor g, Representable g r) => Applicative (StoreT {r} g w) where
  pure a = MkStoreT (pure (pureRep {r} a)) neutral
  MkStoreT ff m <*> MkStoreT fa n = MkStoreT (apRep {r} <$> ff <*> fa) (m <+> n)

export
implementation (Functor g, Comonad w, Representable g r) => Comonad (StoreT {r} g w) where
  extract (MkStoreT w s) = index {r} (extract w) s
  duplicate (MkStoreT w s) = MkStoreT (extend (tabulate . MkStoreT) w) s

export
implementation (Functor g, Comonad w, Representable g r) => ComonadStore r (StoreT {r} g w) where
  pos (MkStoreT _ s) = s
  peek s (MkStoreT w _) = extract w `index` s
  peeks f (MkStoreT w s) = extract w `index` f s
  seek s (MkStoreT w _) = MkStoreT w s
  seeks f (MkStoreT w s) = MkStoreT w (f s)

export
implementation (Functor g, ComonadApply w, Semigroup r, Representable g r) => ComonadApply (StoreT {r} g w) where
  MkStoreT ff m <@> MkStoreT fa n = MkStoreT ((apRep {r} <$> ff) <@> fa) (m <+> n)

export
implementation Representable g r => ComonadTrans (StoreT {r} g) where
  lower (MkStoreT w s) = flip index s <$> w

export
implementation (Functor g, ComonadEnv m w, Representable g r) => ComonadEnv m (StoreT {r} g w) where
  ask = ask . lower

export
implementation (Functor g, ComonadTraced m w, Representable g r) => ComonadTraced m (StoreT {r} g w) where
  trace m = trace m . lower
