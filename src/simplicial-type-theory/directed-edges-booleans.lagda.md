# Directed edges in the booleans

```agda
module simplicial-type-theory.directed-edges-booleans where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-dependent-functions
open import foundation.booleans
open import foundation.cartesian-product-types
open import foundation.contractible-types
open import foundation.dependent-identifications
open import foundation.dependent-pair-types
open import foundation.equality-cartesian-product-types
open import foundation.equality-dependent-pair-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.homotopy-induction
open import foundation.identity-types
open import foundation.negated-equality
open import foundation.negation
open import foundation.retractions
open import foundation.sections
open import foundation.structure-identity-principle
open import foundation.torsorial-type-families
open import foundation.universe-levels

open import orthogonal-factorization-systems.extensions-of-maps

open import simplicial-type-theory.action-on-directed-edges-dependent-functions
open import simplicial-type-theory.action-on-directed-edges-functions
open import simplicial-type-theory.dependent-simplicial-edges
open import simplicial-type-theory.directed-edges
open import simplicial-type-theory.directed-interval-type
open import simplicial-type-theory.simplicial-arrows
open import simplicial-type-theory.simplicially-discrete-types
```

</details>

## Idea

We postulate that the [booleans](foundation.booleans.md) are
[simplicially discrete](simplicial-type-theory.simplicially-discrete-types.md)
and hence that all [directed edges](simplicial-type-theory.directed-edges.md)
are constant. This refutes the models of the
[directed interval](simplicial-type-theory.directed-interval.md) in the booleans
and is a differing property between the two types.

As a corollary we have that the universe of simplicially discrete types is
closed under finite coproducts.

## Postulate

```agda
postulate
  is-simplicially-discrete-bool : is-simplicially-discrete bool
```

## Properties

### The booleans are not a directed interval

```agda
is-not-directed-interval-bool' : bool ≠ 𝟚
is-not-directed-interval-bool' =
  nonequal-leibniz
    ( is-simplicially-discrete)
    ( bool)
    ( 𝟚)
    ( is-simplicially-discrete-bool)
    ( is-not-simplicially-discrete-𝟚)

-- is-not-directed-interval-bool : ¬ (bool ≃ 𝟚)
-- is-not-directed-interval-bool e = {!   !}
```
