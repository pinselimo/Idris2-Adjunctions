module Data.Functor1.Applied

import Data.Functor1

public export
record Applied a f where
  constructor Apply
  runApplied : f a

export
Functor1 (Applied a) where
  map1 f = Apply . f . runApplied

