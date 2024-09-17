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
open import foundation.coproduct-types
open import foundation.dependent-identifications
open import foundation.dependent-pair-types
open import foundation.equality-cartesian-product-types
open import foundation.equality-dependent-pair-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.functoriality-coproduct-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.homotopy-induction
open import foundation.identity-types
open import foundation.negated-equality
open import foundation.negation
open import foundation.raising-universe-levels
open import foundation.retractions
open import foundation.retracts-of-types
open import foundation.sections
open import foundation.structure-identity-principle
open import foundation.torsorial-type-families
open import foundation.type-arithmetic-booleans
open import foundation.unit-type
open import foundation.universal-property-booleans
open import foundation.universe-levels

open import orthogonal-factorization-systems.coproducts-null-types
open import orthogonal-factorization-systems.extensions-of-maps
open import orthogonal-factorization-systems.null-families-of-types
open import orthogonal-factorization-systems.null-maps
open import orthogonal-factorization-systems.null-types
open import orthogonal-factorization-systems.orthogonal-maps

open import simplicial-type-theory.action-on-directed-edges-dependent-functions
open import simplicial-type-theory.action-on-directed-edges-functions
open import simplicial-type-theory.dependent-directed-edges
open import simplicial-type-theory.directed-edges
open import simplicial-type-theory.directed-interval-type
open import simplicial-type-theory.simplicial-arrows
open import simplicial-type-theory.simplicially-discrete-types
```

</details>

## Idea

We postulate that the [booleans](foundation.booleans.md) are
[simplicially discrete](simplicial-type-theory.simplicially-discrete-types.md)
and hence that all its
[directed edges](simplicial-type-theory.directed-edges.md) are constant. This
refutes the models of the
[directed interval](simplicial-type-theory.directed-interval.md) in the booleans
and is a distinguishing property between the two.

As a corollary we have that the universe of simplicially discrete types is
closed under finite coproducts and contains the finite types.

## Postulate

```agda
postulate
  is-simplicially-discrete-bool : is-simplicially-discrete bool
```

## Properties

### The booleans are 𝟚-null

```agda
is-𝟚-null-bool : is-null 𝟚 bool
is-𝟚-null-bool =
  is-𝟚-null-is-simplicially-discrete is-simplicially-discrete-bool
```

### The booleans are not a directed interval

```agda
is-not-directed-interval-bool' : 𝟚 ≠ bool
is-not-directed-interval-bool' =
  nonequal-leibniz'
    ( is-simplicially-discrete)
    ( 𝟚)
    ( bool)
    ( is-not-simplicially-discrete-𝟚)
    ( is-simplicially-discrete-bool)

is-not-directed-interval-bool : ¬ (𝟚 ≃ bool)
is-not-directed-interval-bool e =
  is-not-simplicially-discrete-𝟚
    ( is-simplicially-discrete-equiv e is-simplicially-discrete-bool)

is-not-retract-of-directed-interval-bool : ¬ (𝟚 retract-of bool)
is-not-retract-of-directed-interval-bool r =
  is-not-simplicially-discrete-𝟚
    ( is-simplicially-discrete-retract r is-simplicially-discrete-bool)
```

### Coproducts of simplicially discrete types are simplicially discrete

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  (is-disc-A : is-simplicially-discrete A)
  (is-disc-B : is-simplicially-discrete B)
  where

  is-simplicially-discrete-coproduct :
    is-simplicially-discrete A →
    is-simplicially-discrete B →
    is-simplicially-discrete (A + B)
  is-simplicially-discrete-coproduct is-disc-A is-disc-B =
    is-simplicially-discrete-is-𝟚-null
      ( is-null-coproduct-is-null-bool 𝟚
        ( is-𝟚-null-bool)
        ( is-𝟚-null-is-simplicially-discrete is-disc-A)
        ( is-𝟚-null-is-simplicially-discrete is-disc-B))
```

### Finite types are simplicially discrete

> This remains to be formalized.

### The directed interval is not finite

> This remains to be formalized.
