# The simplicial spines

```agda
module simplicial-type-theory.simplicial-spines where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.booleans
open import foundation.cartesian-product-types
open import foundation.conjunction
open import foundation.coproduct-types
open import foundation.dependent-identifications
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
open import foundation.retractions
open import foundation.sections
open import foundation.sets
open import foundation.subtypes
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.unit-type
open import foundation.universe-levels

open import simplicial-type-theory.directed-interval-type
open import simplicial-type-theory.directed-relation-directed-interval-type
open import simplicial-type-theory.simplicial-arrows
open import simplicial-type-theory.directed-edges

open import synthetic-homotopy-theory.cocones-under-spans
open import synthetic-homotopy-theory.dependent-cocones-under-spans
open import synthetic-homotopy-theory.joins-of-types
open import synthetic-homotopy-theory.pushouts
```

</details>

## Idea

The `n`-spine is the iterated [pushout](synthetic-homotopy-theory.pushouts.md)

```text
         0
    1 ------> spine n
    |            |
  1 |            |
    ∨          ⌜ ∨
    𝟚 ------> spine (n + 1)
```

where

```text
  spine 0 := 1.
```
