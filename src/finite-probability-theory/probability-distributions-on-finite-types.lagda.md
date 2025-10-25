# Probability distributions on finite types

```agda
module finite-probability-theory.probability-distributions-on-finite-types where
```

<details><summary>Imports</summary>

```agda
open import finite-probability-theory.positive-distributions-on-finite-types

open import foundation.empty-types
open import foundation.function-types
open import foundation.identity-types
open import foundation.inhabited-types
open import foundation.propositions
open import foundation.sets
open import foundation.subtypes
open import foundation.universe-levels

open import group-theory.sums-of-finite-families-of-elements-abelian-groups

open import real-numbers.addition-real-numbers
open import real-numbers.dedekind-real-numbers
open import real-numbers.positive-real-numbers
open import real-numbers.rational-real-numbers

open import univalent-combinatorics.finite-types
```

</details>

## Idea

A
{{#concept "probability distribution" Disambiguation="on a finite type" Agda=probability-distribution-Finite-Type}}
on a [finite type](univalent-combinatorics.finite-types.md) is a
[positive distribution](finite-probability-theory.positive-distributions-on-finite-types.md)
with total measure equal to 1.

## Definition

### The property of being a probability distribution on a finite type

```agda
module _
  {l : Level} (Ω : Finite-Type l) (μ : positive-distribution-Finite-Type Ω)
  where

  is-probability-distribution-prop-positive-distribution-Finite-Type :
    Prop (lsuc lzero)
  is-probability-distribution-prop-positive-distribution-Finite-Type =
    Id-Prop
      ( ℝ-Set lzero)
      ( total-measure-positive-distribution-Finite-Type Ω μ)
      ( one-ℝ)

  is-probability-distribution-positive-distribution-Finite-Type :
    UU (lsuc lzero)
  is-probability-distribution-positive-distribution-Finite-Type =
    type-Prop is-probability-distribution-prop-positive-distribution-Finite-Type

  is-prop-is-probability-distribution-Finite-Type :
    is-prop is-probability-distribution-positive-distribution-Finite-Type
  is-prop-is-probability-distribution-Finite-Type =
    is-prop-type-Prop
      is-probability-distribution-prop-positive-distribution-Finite-Type
```

### Probability distributions on finite types

```agda
module _
  {l : Level} (Ω : Finite-Type l)
  where

  probability-distribution-Finite-Type : UU (lsuc lzero ⊔ l)
  probability-distribution-Finite-Type =
    type-subtype
      ( is-probability-distribution-prop-positive-distribution-Finite-Type Ω)
```
