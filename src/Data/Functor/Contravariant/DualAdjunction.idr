module Data.Functor.Contravariant.DualAdjunction 

import Data.Contravariant

public export
interface (Contravariant f, Contravariant g) => DualAdjunction f g where
  unitOp : g (f a) -> a
  unitOp = leftAdjunctOp {f} id
  
  counitOp : f (g a) -> a
  counitOp = rightAdjunctOp id
  
  leftAdjunctOp : (f a -> b) -> g b -> a
  leftAdjunctOp h = unitOp {f} . contramap h

  rightAdjunctOp : (g b -> a) -> f a -> b
  rightAdjunctOp f = counitOp . contramap f

