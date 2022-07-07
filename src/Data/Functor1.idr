module Data.Functor1

import Control.Monad.Identity

||| 'map1' f . 'map1' g = 'map1' (f . g)
||| 'map1' id = id
public export
interface Functor1 (0 w : (Type -> Type) -> Type) where
  map1 : (forall a. f a -> g a) -> w f -> w g

export
map1Identity : Functor1 w => (forall x. f x -> x) -> w f -> w Identity
map1Identity f = map1 (Id . f)

-- TODO: Use profunctors Proxy
public export
record Proxy (a : (Type -> Type)) where
  constructor MkProxy

export
implementation Functor1 Proxy where
  map1 _ = const MkProxy

-- TODO: Use base Const
public export
record Const (a : Type) (b : Type -> Type) where
  constructor MkConst
  runConst : a 

export
implementation Functor1 (Const a) where
  map1 _ = MkConst . runConst
