# Simplicial discreteness of the booleans

```agda
open import foundation.booleans
open import foundation.universe-levels
open import order-theory.nontrivial-bounded-total-orders
import simplicial-type-theory.discrete-types

module
  simplicial-type-theory.discreteness-booleans
  {I1 I2 : Level} (I : Nontrivial-Bounded-Total-Order I1 I2)
  (let open simplicial-type-theory.discrete-types I)
  (is-discrete▵-bool : is-discrete▵ bool)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-dependent-functions
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
open import orthogonal-factorization-systems.extensions-maps
open import orthogonal-factorization-systems.null-families-of-types
open import orthogonal-factorization-systems.null-types
open import orthogonal-factorization-systems.orthogonal-maps

open import simplicial-type-theory.action-on-directed-edges-dependent-functions I
open import simplicial-type-theory.action-on-directed-edges-functions I
open import simplicial-type-theory.arrows I
open import simplicial-type-theory.dependent-directed-edges I
open import simplicial-type-theory.directed-edges I
open import simplicial-type-theory.directed-interval I
```

</details>

## Idea

If we assume that the [booleans](foundation.booleans.md) are
[simplicially discrete](simplicial-type-theory.discrete-types.md) and hence that
all its [directed edges](simplicial-type-theory.directed-edges.md) are constant,
we refute the models of the
[directed interval](simplicial-type-theory.directed-interval.md) in the
booleans, as this gives a distinguishing property between `Δ¹` and `bool`. As a
corollary we have that the universe of simplicially discrete types is closed
under finite coproducts and contains the finite types.

## Properties

### The booleans are Δ¹-null

```agda
is-Δ¹-null-bool : is-null Δ¹ bool
is-Δ¹-null-bool =
  is-Δ¹-null-is-discrete▵ is-discrete▵-bool
```

### The booleans are not a directed interval

```agda
is-not-directed-interval-bool : ¬ (Δ¹ ≃ bool)
is-not-directed-interval-bool e =
  is-not-discrete▵-Δ¹
    ( is-discrete▵-equiv e is-discrete▵-bool)

is-not-retract-of-directed-interval-bool : ¬ (Δ¹ retract-of bool)
is-not-retract-of-directed-interval-bool r =
  is-not-discrete▵-Δ¹
    ( is-discrete▵-retract r is-discrete▵-bool)
```

### Coproducts of simplicially discrete types are simplicially discrete

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  (is-disc-A : is-discrete▵ A)
  (is-disc-B : is-discrete▵ B)
  where

  is-discrete▵-coproduct :
    is-discrete▵ A →
    is-discrete▵ B →
    is-discrete▵ (A + B)
  is-discrete▵-coproduct is-disc-A is-disc-B =
    is-discrete▵-is-Δ¹-null
      ( is-null-coproduct-is-null-bool Δ¹
        ( is-Δ¹-null-bool)
        ( is-Δ¹-null-is-discrete▵ is-disc-A)
        ( is-Δ¹-null-is-discrete▵ is-disc-B))
```

### Finite types are simplicially discrete

> This remains to be formalized.

### The directed interval is not finite

> This remains to be formalized.
