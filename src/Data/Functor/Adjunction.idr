module Data.Functor.Adjunction

import Control.Monad.Identity
import Data.Morphisms
import Data.Profunctor

import Data.Functor.Rep
import Data.Functor.Sum
import Data.Functor.Product

public export
interface (Functor f, Functor u, Representable u r) => Adjunction f u r where
  unit : a -> u (f a)
  unit = leftAdjunct {u=u, r=r} id
  counit : f (u a) -> a
  counit = rightAdjunct {r=r} id
  leftAdjunct : (f a -> b) -> a -> u b
  leftAdjunct f = map f . unit {u=u, r=r}
  rightAdjunct : (a -> u b) -> f a -> b
  rightAdjunct f = counit {r=r} . map f

%inline
export
adjuncted : (Adjunction f u r, Profunctor p, Functor g)
         => p (a -> u b) (g (c -> u d)) -> p (f a -> b) (g (f c -> d))
adjuncted = dimap (leftAdjunct {r=r}) (map (rightAdjunct {r=r}))

export
tabulateAdjunction : Adjunction f u r => (f () -> b) -> u b
tabulateAdjunction f = leftAdjunct {r=r} f ()

export
indexAdjunction : Adjunction f u r => u b -> f a -> b
indexAdjunction = rightAdjunct {r=r} . const

export
zapWithAdjunction : Adjunction f u r => (a -> b -> c) -> u a -> f b -> c
zapWithAdjunction f ua = rightAdjunct {r=r} $ \b => map (flip f b) ua

export
splitL : Adjunction f u r => f a -> (a, f ())
splitL = rightAdjunct {r=r} $ flip (leftAdjunct {u=u, r=r}) () . (,)

export
unsplitL : Functor f => a -> f () -> f a
unsplitL = (<$)

export
extractL : Adjunction f u r => f a -> a
extractL = fst . splitL {u=u, r=r}

export
duplicateL : Adjunction f u r => f a -> f (f a)
duplicateL as = as <$ as

export
zipR : Adjunction f u r => (u a, u b) -> u (a, b)
zipR = leftAdjunct {f=f, r=r} $ \f => (counit {r=r} $ map fst f, counit {r=r} $ map snd f)

export
unzipR : Functor u => u (a, b) -> (u a, u b)
unzipR f = (map fst f, map snd f)

export
absurdL : {auto f : Type -> Type} -> Void -> f Void
absurdL = absurd

export
unabsurdL : Adjunction f u r => f Void -> Void
unabsurdL = rightAdjunct {u=u, r=r} absurd

export
cozipL : (Monad f, Adjunction f u r) => f (Either a b) -> Either (f a) (f b)
cozipL = rightAdjunct {u=u, r=r} $ \x => either (leftAdjunct {u=u, r=r} Left) (leftAdjunct {u=u, r=r} Right) x

export
uncozipL : Functor f => Either (f a) (f b) -> f (Either a b)
uncozipL = either (map Left) (map Right)

export
implementation Adjunction Identity Identity () where
  leftAdjunct f  = Id . f . Id
  rightAdjunct f = runIdentity . f . runIdentity
