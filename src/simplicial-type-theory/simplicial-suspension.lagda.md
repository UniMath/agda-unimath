# The simplicial suspension

```agda
module simplicial-type-theory.simplicial-suspension where
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

open import simplicial-type-theory.directed-interval-type
open import simplicial-type-theory.directed-relation-on-directed-interval-type
open import simplicial-type-theory.simplicial-arrows

open import synthetic-homotopy-theory.cocones-under-spans
open import synthetic-homotopy-theory.joins-of-types
open import synthetic-homotopy-theory.pushouts
```

</details>

## Idea

Given a type `X`, we define the {{#concept "simplicial suspension"}} of `X` as
the [pushout](synthetic-homotopy-theory.pushouts.md)

```text
           id × 0₂ + id × 1₂
    X + X ------------------> X × 𝟚
      |                         |
      |                         |
      ∨                       ⌜ ∨
      2 --------------------> Σ₂ X
```

Intuitively, the simplicial suspension of `X` can be understood as a type
consisting of a point at the north and south pole, and a
[simplicial edge](simplicial-type-theory.simplicial-edges.md) `north →₂ south`
for every element `x : X`. It is constructed by taking the
[cartesian product](foundation-core.cartesian-product-types.md) `X × 𝟚`, and
"pinching" it together at the north and south pole.
