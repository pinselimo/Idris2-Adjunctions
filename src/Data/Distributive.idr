module Data.Distributive

import Control.Monad.Identity
import Control.Monad.Reader.Reader
import Data.Morphisms
import Data.Profunctor -- Tagged
import Data.Proxy

import Data.Functor.Product

public export
interface Functor g => Distributive g where
  distribute : Functor f => f (g a) -> g (f a)
  distribute = collect id

  collect : Functor f => (a -> g b) -> f a -> g (f b)
  collect f = distribute . map f

export
cotraverse : (Distributive g, Functor f) => (f a -> b) -> f (g a) -> g b
cotraverse f = map f . distribute

export
implementation Distributive Identity where
  collect x = Id . map (runIdentity . x)

export
implementation Distributive Proxy where
  distribute _ = MkProxy
  collect _ _ = MkProxy

export
implementation Distributive (Morphism e) where
  distribute a = Mor $ \e => flip applyMor e <$> a
  collect  f q = Mor $ \e => flip applyMor e . f <$> q

export
implementation (Distributive g, Functor g) => Distributive (ReaderT e g) where
  distribute a = MkReaderT $ \e => collect (runReaderT e) a
  collect f x = MkReaderT $ \e => collect (\a => runReaderT e (f a)) x

export
implementation Distributive (Tagged t) where
  distribute = Tag . map runTagged
  collect f  = Tag . map (runTagged . f)

export
implementation (Distributive f, Distributive g) => Distributive (Product f g) where
  distribute wp = Pair (collect fstP wp) (collect sndP wp)
    where fstP : Product f g a -> f a
          fstP (Pair f _) = f
          sndP : Product f g a -> g a
          sndP (Pair _ g) = g

namespace Distributive
  public export
  [Compose] (Distributive f, Distributive g) => Distributive (f . g)
    using Functor.Compose where
      collect f = map distribute . distribute . map f
      distribute = map distribute . distribute

