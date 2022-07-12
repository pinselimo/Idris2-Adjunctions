Idris2 Adjunctions and Representable Functors
=============================================

This is a adjunction library for Idris2 and aims to be a cromprehensive port of Edward Kmett's [Haskell Adjunctions](https://github.com/ekmett/profunctors).  Contributions, bug reports, and feature requests are welcome.

Contains
--------

  * Adjunctions

  * Contravariant Adjunctions

  * Distributive Functors

  * Functor Sums and Products

  * Adjoint Monads and Comonads

  * Representable Monads and Comonads

Installation
------------

Run `idris2 --install adjunctions.ipkg` from inside this directory, and then if
you want to use it with anything, invoke Idris with `-p adjunctions` (i.e.
`idris2 -p adjunctions hack_the_planet.idr`)
