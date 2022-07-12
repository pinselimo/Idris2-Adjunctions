module Data.Functor.Rep

import Control.Comonad
import Control.Comonad.Trans
import Control.Monad.Identity
import Control.Monad.Reader
import Data.Morphisms
import Data.Profunctor
import Data.Proxy

import Data.Distributive
import Data.Functor1
import Data.Functor.Product

public export
interface Distributive f => Representable f r where
  tabulate : (r -> a) -> f a
  index : f a -> r -> a

export
tabulateAlg : Representable f r => ((forall x. f x -> x) -> a) -> f a
tabulateAlg f = tabulate $ \i => f $ flip (index {r}) i

export
cotraverse1 : (Functor1 w, Representable f r) => (w Identity -> a) -> w f -> f a
cotraverse1 f w = tabulateAlg {r} (f . flip map1Identity w)

export
distribute1 : (Functor1 w, Representable f r) => w f -> f (w Identity)
distribute1 = cotraverse1 {r} id

export
collect1 : (Functor1 w, Representable f r) => (forall x. g x -> f x) -> w g -> f (w Identity)
collect1 f = distribute1 {r} . map1 f

export
cotraverseMap1 : (Functor1 w, Representable f r) => (w Identity -> a) -> (forall x. g x -> f x) -> w g -> f a
cotraverseMap1 f g = cotraverse1 {r} f . map1 g

data PairOf : (a : Type) -> (b : Type) -> (f : Type -> Type) -> Type where
  MkPairOf : f a -> f b -> PairOf a b f
implementation Functor1 (PairOf a b) where
  map1 f (MkPairOf x y) = MkPairOf (f x) (f y)

export
mzipWithRep : Representable f r => (a -> b -> c) -> f a -> f b -> f c
mzipWithRep f as bs =
  cotraverse1 {r} (\(MkPairOf (Id a) (Id b)) => f a b) (MkPairOf as bs)

export
mzipRep : Representable f r => f a -> f b -> f (a, b)
mzipRep = mzipWithRep {r} (,)

%inline
export
tabulated : (Representable f r, Representable g r', Profunctor p, Functor h)
          => p (f a) (h (g b)) -> p (r -> a) (h (r' -> b))
tabulated = dimap (tabulate {r}) (map (index {r=r'}))

-- Default definitions
export
mapRep : Representable f r => (a -> b) -> f a -> f b
mapRep = map

export
pureRep : Representable f r => a -> f a
pureRep = tabulate {r} . const

export
apRep : Representable f r => f (a -> b) -> f a -> f b
apRep = mzipWithRep {r} ($)

export
askRep : Representable f r => f r
askRep = tabulate id

export
joinRep : Representable f r => f (f a) -> f a
joinRep ffa = apRep {r} (map (index {r}) ffa) askRep

export
bindRep : Representable f r => f a -> (a -> f b) -> f b
bindRep m = joinRep {r} . (<$> m)

export
localRep : Representable f r => (r -> r) -> f a -> f a
localRep f m = tabulate (index m . f)

public export
record Composed (g : Type -> Type) (a : Type) (f : Type -> Type) where
  constructor Compose
  runComposed : g (f a)

export
implementation Functor g => Functor1 (Composed g a) where
  map1 f = Compose . map f . runComposed

export
cotraverseRep : (Representable f r, Functor w) => (w a -> b) -> w (f a) -> f b
cotraverseRep f = cotraverse1 {r} (f . map runIdentity . runComposed) . (Compose {g=w})

export
distributeRep : (Representable f r, Functor w) => w (f a) -> f (w a)
distributeRep = cotraverseRep {r} id

export
collectRep : (Representable f r, Functor w) => (a -> f b) -> w a -> f (w b)
collectRep f = distributeRep {r} . map f

export
duplicateRepBy : Representable f r => (r -> r -> r) -> f a -> f (f a)
duplicateRepBy plus w = tabulate (\m => tabulate (index w . plus m))

export
extendRepBy : Representable f r => (r -> r -> r) -> (f a -> b) -> f a -> f b
extendRepBy plus f w = tabulate (\m => f (tabulate (index w . plus m)))

export
extractRepBy : Representable f r => r -> f a -> a
extractRepBy = flip index

export
duplicatedRep : (Representable f r, Semigroup r) => f a -> f (f a)
duplicatedRep = duplicateRepBy {r} (<+>)

export
extendedRep : (Representable f r, Semigroup r) => (f a -> b) -> f a -> f b
extendedRep = extendRepBy {r} (<+>)

export
duplicateRep : (Representable f r, Monoid r) => f a -> f (f a)
duplicateRep = duplicateRepBy {r} (<+>)

export
extendRep : (Representable f r, Monoid r) => (f a -> b) -> f a -> f b
extendRep = extendRepBy {r} (<+>)

export
extractRep : (Representable f r, Monoid r) => f a -> a
extractRep = extractRepBy {r} neutral

export
imapRep : Representable f r => (r -> a -> b) -> f a -> f b
imapRep f = mzipWithRep {r} f (askRep {r})

export
ifoldMapRep : (Representable f r, Foldable f, Monoid m)
            => (r -> a -> m) -> (f a -> m)
ifoldMapRep ix = (foldMap id) . imapRep ix

export
itraverseRep : (Representable g r, Traversable g, Applicative f)
             => (r -> a -> f a') -> (g a -> f (g a'))
itraverseRep ix = sequence . imapRep ix

-- Logatithms
public export
record Logarithm f where
  constructor Log
  runLogarithm : forall x. f x -> x

export
contramapLogarithm : (forall x. f x -> g x) -> Logarithm g -> Logarithm f
contramapLogarithm f (Log g) = Log (g . f)

export
logarithmRep : (Representable f r, Representable g r', Profunctor p, Functor h)
             => p r (h r') -> p (Logarithm f) (h (Logarithm g))
logarithmRep = dimap (\lf => (runLogarithm lf) askRep) (map (\x => Log (`index` x)))

-- Tabulation
export
record TabulateArg a f where
  constructor MkTabulateArg
  runTabulateArg : Logarithm f -> a

export
implementation Functor1 (TabulateArg a) where
  map1 f (MkTabulateArg g) = MkTabulateArg (g . contramapLogarithm f)

export
tabulateCotraverse1 : Representable f r => (Logarithm f -> a) -> f a
tabulateCotraverse1 =
  cotraverse1 {r} (\(MkTabulateArg g) => g (Log runIdentity)) . MkTabulateArg

export
indexLogarithm : f a -> Logarithm f -> a
indexLogarithm i (Log f) = f i

export
cotraverse1Iso : (Representable g r, Functor1 w)
  => (forall x. f x -> g x)
  -> (forall x. g x -> f x)
  -> (w Identity -> a)
  -> w f
  -> f a
cotraverse1Iso t frm f = frm . cotraverseMap1 {r} f t

-- Implementations
export
implementation Representable Proxy Void where
  index MkProxy = absurd
  tabulate _ = MkProxy

export
implementation Representable Identity () where
  index (Id a) () = a
  tabulate f = Id (f ())

export
implementation Representable (Tagged a) () where
  index (Tag a) () = a
  tabulate f = Tag (f ())

export
implementation Representable (Morphism e) e where
  index = applyMor
  tabulate = Mor

export
implementation Representable m r => Representable (ReaderT e m) (e, r) where
  index (MkReaderT f) (e, k) = index (f e) k
  tabulate f = MkReaderT $ tabulate . curry f

namespace Representable
  public export
  [Compose] (Representable f r, Representable g r') => Representable (f . g) (r, r')
    using Distributive.Compose where
      index fg (i, j) = index (index fg i) j
      tabulate f = tabulate $ tabulate . curry f

export
implementation (Representable f r, Representable g r') => Representable (Product f g) (Either r r') where
  index (Pair a _) (Left i)  = index a i
  index (Pair _ b) (Right j) = index b j
  tabulate f = Pair (tabulate (f . Left)) (tabulate (f . Right))

public export
record Co (f : Type -> Type) (a : Type) where
  constructor MkCo
  unCo : f a

export
implementation Functor f => Functor (Co f) where
  map f = MkCo . map f . unCo

export
implementation Distributive f => Distributive (Co f) where
  distribute = MkCo . distribute . map unCo

export
implementation Representable f r => Representable (Co f) r where
  tabulate = MkCo . tabulate
  index = index . unCo

export
implementation Representable f r => Applicative (Co f) where
  pure = pureRep {r}
  (<*>) = apRep {r}

export
implementation Representable f r => Monad (Co f) where
  (>>=) = bindRep {r}
  join a = bindRep {r} a id

export
implementation Representable f r => MonadReader r (Co f) where
  ask = askRep {r}
  local = localRep {r}

export
implementation (Representable f r, Monoid r) => Comonad (Co f) where
  extract = extractRep {r}
  extend = extendRep {r}
  duplicate = duplicateRep {r}

export
implementation ComonadTrans Co where
  lower (MkCo f) = f

export
liftR2 : Representable f r => (a -> b -> c) -> f a -> f b -> f c
liftR2 = mzipWithRep {r}

public export
data TripleOf : (a : Type) -> (b : Type) -> (c : Type) -> (f : Type -> Type) -> Type where
  MkTripleOf : (f a) -> (f b) -> (f c) -> TripleOf a b c f

export
implementation Functor1 (TripleOf a b c) where
  map1 f (MkTripleOf a b c) = MkTripleOf (f a) (f b) (f c)

export
liftR3 : Representable f r => (a -> b -> c -> d) -> f a -> f b -> f c -> f d
liftR3 f fa fb fc = cotraverse1 {r} (\(MkTripleOf (Id a) (Id b) (Id c)) => f a b c) (MkTripleOf fa fb fc)

