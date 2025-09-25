# The directed suspension

```agda
open import foundation.universe-levels
open import order-theory.nontrivial-bounded-total-orders

module
  simplicial-type-theory.directed-suspension
  {I1 I2 : Level} (I : Nontrivial-Bounded-Total-Order I1 I2)
  where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.booleans
open import foundation.cartesian-product-types
open import foundation.conjunction
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.disjunction
open import foundation.empty-types
open import foundation.equality-dependent-pair-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.subtypes
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.unit-type
open import foundation.universe-levels

open import simplicial-type-theory.arrows I
open import simplicial-type-theory.directed-interval I
open import simplicial-type-theory.inequality-directed-interval I

open import synthetic-homotopy-theory.cocones-under-spans
open import synthetic-homotopy-theory.joins-of-types
open import synthetic-homotopy-theory.pushouts
```

</details>

## Idea

Given a type `X`, we define the {{#concept "directed suspension"}} of `X` as the
[pushout](synthetic-homotopy-theory.pushouts.md)

```text
           id × 0▵ + id × 1▵
    X + X ------------------> X × Δ¹
      |                         |
      |                         |
      ∨                       ⌜ ∨
     ∂Δ¹ ---------------------> Σ▵X.
```

or in other words the oriented pushout

```text
  X ------> 1
  |         |
  |    ⇗    |
  ∨       ⌜ ∨
  1 -----> Σ▵X.
```

Intuitively, the directed suspension of `X` can be understood as a type
consisting of a point at the north and south pole, and a
[directed edge](simplicial-type-theory.directed-edges.md) `north →▵ south` for
every element `x : X`. It is constructed by taking the
[cartesian product](foundation-core.cartesian-product-types.md) `X × Δ¹`, and
"pinching" it together at the north and south pole.

## Definitions

> This remains to be formalized.
