module Data.Functor.Contravariant.Yoneda

import Data.Contravariant

import Data.Functor.Contravariant.Adjunction
import Data.Functor.Contravariant.Rep

public export
record YonedaT f a where
  constructor MkYonedaT
  runYonedaT : forall b. (b -> a) -> f b

export
liftYonedaT : Contravariant f => f a -> YonedaT f a
liftYonedaT a = MkYonedaT (\f => contramap f a)

export
lowerYonedaT : YonedaT f a -> f a
lowerYonedaT (MkYonedaT f) = f id

export
implementation Contravariant (YonedaT f) where
  contramap f m = MkYonedaT (\k => runYonedaT m (f . k))

export
implementation Representable f r => Representable (YonedaT f) r where
  index  = index . lowerYonedaT
  tabulate = liftYonedaT . tabulate

export
implementation (Functor g, Functor f, Adjunction f g r) => Adjunction (YonedaT f) (YonedaT g) r where
  unit = liftYonedaT . contramap lowerYonedaT . unit {g, r}
  counit = liftYonedaT . contramap lowerYonedaT . counit {r}
  leftAdjunct h = liftYonedaT . contramap h . map liftYonedaT . unit {g, r}
  rightAdjunct h = liftYonedaT . contramap h . map liftYonedaT . counit {f, r}

export
implementation Eq (f a) => Eq (YonedaT f a) where
  MkYonedaT f == MkYonedaT g = f id == g id

export
implementation Ord (f a) => Ord (YonedaT f a) where
  MkYonedaT f `compare` MkYonedaT g = f id `compare` g id

%inline
export
maxF : (Contravariant f, Ord (f a)) => YonedaT f a -> YonedaT f a -> YonedaT f a
MkYonedaT f `maxF` MkYonedaT g = liftYonedaT $ f id `max` g id

%inline
export
minF : (Contravariant f, Ord (f a)) => YonedaT f a -> YonedaT f a -> YonedaT f a
MkYonedaT f `minF` MkYonedaT g = liftYonedaT $ f id `min` g id
