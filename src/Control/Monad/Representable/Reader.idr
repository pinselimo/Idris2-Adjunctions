module Control.Monad.Representable.Reader

import Control.Comonad
import Control.Monad.Identity
import Control.Monad.Reader
import Control.Monad.Trans
import Control.Monad.Writer
import Data.Morphisms

import Data.Distributive
import Data.Functor.Rep

%hide Control.Monad.Reader.ReaderT

public export
record ReaderT (f : Type -> Type) (m : Type -> Type) (b : Type) where
  constructor MkReaderT
  getReaderT : f (m b)

public export
Reader : (Type -> Type) -> Type -> Type
Reader f = ReaderT f Identity

export
readerT : Representable f r => (r -> m b) -> ReaderT f m b
readerT = MkReaderT . tabulate

export
runReaderT : Representable f r => ReaderT f m b -> r -> m b
runReaderT = index . getReaderT

export
implementation (Functor f, Functor m) => Functor (ReaderT f m) where
  map f = MkReaderT . map (map f) . getReaderT

export
implementation (Representable f r, Distributive m) => Distributive (ReaderT f m) where
  distribute = MkReaderT . map distribute . collect getReaderT
  collect f = MkReaderT . map distribute . collect (getReaderT . f)

export
implementation (Representable m r', Representable f r, Distributive (ReaderT f m))
  => Representable (ReaderT f m) (r, r') where
  tabulate = MkReaderT . tabulate . applyMor . map tabulate . Mor . curry
  index = uncurry . index . map index . getReaderT

export
implementation (Representable f r, Applicative m) => Applicative (ReaderT f m) where
  pure = MkReaderT . pureRep {r} . pure
  MkReaderT ff <*> MkReaderT fa = MkReaderT $ apRep {r} ((<*>) <$> ff) fa

export
implementation (Representable f r, Monad m) => Monad (ReaderT f m) where
  MkReaderT fm >>= f = MkReaderT $ mzipWithRep {r} (>>=) fm $ applyMor <$> distribute (Mor $ getReaderT . f)
  join (MkReaderT fm) = MkReaderT $  mzipWithRep {r} (>>=) fm $ applyMor <$> distribute (Mor $ getReaderT . id)

export
implementation (Representable f r, Monad m) => MonadReader r (ReaderT f m) where
  ask = MkReaderT (tabulate pure)
  local f m = readerT $ \r => runReaderT m (f r)

export
implementation Representable f r => MonadTrans (ReaderT f) where
  lift = MkReaderT . pureRep {r}

export
implementation (Representable (ReaderT f m) (r, r'), Monoid r, Monoid r') => Comonad (ReaderT f m) where
  extend = extendRep {r=(r,r')}
  duplicate = duplicateRep {r=(r, r')}
  extract = extractRep {r=(r, r')}

export
implementation (Representable f r, HasIO m) => HasIO (ReaderT f m) where
  liftIO = MkReaderT . pureRep {r} . liftIO

export
implementation (Representable f r, MonadWriter w m, Monad (ReaderT f m)) => MonadWriter w (ReaderT f m) where
  writer (a, w) = (MkReaderT . pureRep {r} . tell) w >> pure a
  tell = MkReaderT . pureRep {r} . tell
  listen = MkReaderT . map listen . getReaderT
  pass = MkReaderT . map pass . getReaderT

export
implementation (Foldable f, Foldable m) => Foldable (ReaderT f m) where
  foldr f z = foldr (flip $ foldr f) z . getReaderT
  foldMap f = foldMap (foldMap f) . getReaderT

export
implementation (Traversable f, Traversable m) => Traversable (ReaderT f m) where
  traverse f = map MkReaderT . traverse (traverse f) . getReaderT
