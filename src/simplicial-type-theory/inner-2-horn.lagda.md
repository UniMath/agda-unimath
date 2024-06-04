# The inner 2-horn

```agda
module simplicial-type-theory.inner-2-horn where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.booleans
open import foundation.cartesian-product-types
open import foundation.conjunction
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

open import simplicial-type-theory.directed-edges
open import simplicial-type-theory.directed-interval-type
open import simplicial-type-theory.inequality-directed-interval-type
open import simplicial-type-theory.simplicial-arrows

open import synthetic-homotopy-theory.cocones-under-spans
open import synthetic-homotopy-theory.joins-of-types
open import synthetic-homotopy-theory.pushouts
```

</details>

## Idea

The {{#concept "inner 2-horn" Disambiguation="simplicial type"}} $Λ²₁$, also
called the _2-1-horn_, is the universal type generated from the data of two
directed edges such that the source of the first is the target of the second,
pictorially:

```text
  0 ----> 1 ----> 2.
```

The inner 2-horn has multiple defining properties:

1. It is the pushout

   ```text
            0₂
        1 -----> 𝟚
        |        |
     1₂ |        |
        ∨      ⌜ ∨
        𝟚 -----> Λ²₁.
   ```

2. The inner 2-horn is the subtype of the standard
   [2-simplex](simplicial-type-theory.2-simplices.md) defined by

   ```text
   Λ²₁ = {(x , y) ∈ 𝟚² | (y ＝ 0₂) ∨ (x ＝ 1₂)} ⊆ Δ².
   ```

3. It is the 2-[spine](simplicial-type-theory.spines.md).
