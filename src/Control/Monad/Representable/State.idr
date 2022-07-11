module Control.Monad.Representable.State

import Control.Monad.Identity
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Trans
import Control.Monad.Writer

import Data.Functor.Rep

%hide Control.Monad.State.StateT

public export
record StateT {r : Type} (g : Type -> Type) (m : Type -> Type) (a : Type) where
  constructor MkStateT
  getStateT : g (m (a, r))

export
stateT : Representable g r => (r -> m (a, r)) -> StateT {r} g m a
stateT = MkStateT . tabulate

export
runStateT : Representable g r => StateT {r} g m a -> r -> m (a, r)
runStateT (MkStateT m) = index m

export
mapStateT : Functor g => (m (a, r) -> n (b, r)) -> StateT {r} g m a -> StateT {r} g n b
mapStateT f (MkStateT m) = MkStateT (map f m)

export
evalStateT : (Representable g r, Monad m) => StateT {r} g m a -> r -> m a
evalStateT m s = do
    (a, _) <- runStateT m s
    pure a

export
execStateT : (Representable g r, Monad m) => StateT {r} g m a -> r -> m r
execStateT m s = do
    (_, s') <- runStateT m s
    pure s'

public export
State : {r:Type} -> (Type -> Type) -> Type -> Type
State g = StateT {r} g Identity

export
runState : Representable g r => State {r} g a -> r -> (a, r)
runState m = runIdentity . runStateT m

export
evalState : Representable g r => State {r} g a -> r -> a
evalState m s = fst (runState m s)

export
execState : Representable g r => State {r} g a -> r -> r
execState m s = snd (runState m s)

export
mapState : Functor g => ((a, r) -> (b, r)) -> State {r} g a -> State {r} g b
mapState f = mapStateT (Id . f . runIdentity)

leftAdjunctRep : Representable u r => ((a, r) -> b) -> a -> u b
leftAdjunctRep f a = tabulate (\s => f (a,s))

rightAdjunctRep : Representable u r => (a -> u b) -> (a, r) -> b
rightAdjunctRep f (a, k) = f a `index` k

export
implementation (Functor g, Functor m) => Functor (StateT {r} g m) where
  map f = MkStateT . map (map (\(a, s) => (f a, s))) . getStateT

export
implementation (Representable g r, Functor g, Monad m) => Applicative (StateT {r} g m) where
  pure = MkStateT . leftAdjunctRep pure
  sf <*> sa = stateT $ \r => do
                  (f, r')  <- runStateT sf r
                  map (mapFst f) $ runStateT sa r'

export
implementation (Representable g r, Functor g, Monad m) => Monad (StateT {r} g m) where
  MkStateT m >>= f = MkStateT $ map (>>= rightAdjunctRep (getStateT . f)) m

export
implementation Representable f r => MonadTrans (StateT {r} f) where
  lift m = stateT $ \s => map (\a => (a, s)) m

export
implementation (Representable g r, Functor g, Monad m) => MonadState r (StateT {r} g m) where
  get = stateT $ \s => pure (s, s)
  put s = MkStateT $ pureRep {r} $ pure ((),s)

export
implementation (Representable g r, Functor g, MonadReader e m) => MonadReader e (StateT {r} g m) where
  ask = lift ask
  local = mapStateT . local

export
implementation (Representable g r, Functor g, MonadWriter w m) => MonadWriter w (StateT {r} g m) where
  tell = lift . tell
  listen = mapStateT $ \ma => do
     ((a,s'), w) <- listen ma
     pure ((a,w), s')
  pass = mapStateT $ \ma => pass $ do
    ((a, f), s') <- ma
    pure ((a, s'), f)

export
liftCallCC : Representable g r => ((((a, r) -> m (b, r)) -> m (a, r)) -> m (a, r)) ->
             ((a -> StateT {r} g m b) -> StateT {r} g m a) -> StateT {r} g m a
liftCallCC callCC' f = stateT $ \s =>
    callCC' $ \c =>
    runStateT (f (\a => MkStateT $ pureRep {r} $ c (a, s))) s

export
liftCallCC' : Representable g r => ((((a, r) -> m (b, r)) -> m (a, r)) -> m (a, r)) ->
              ((a -> StateT {r} g m b) -> StateT {r} g m a) -> StateT {r} g m a
liftCallCC' callCC' f = stateT $ \s =>
    callCC' $ \c =>
    runStateT (f (\a => stateT $ \s' => c (a, s'))) s

