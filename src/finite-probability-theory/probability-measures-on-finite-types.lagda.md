# Probability measures on finite types

```agda
module finite-probability-theory.probability-measures-on-finite-types where
```

<details><summary>Imports</summary>

```agda
open import finite-probability-theory.measures-on-finite-types

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
{{#concept "probability measure" Disambiguation="on a finite type" Agda=probability-measure-Finite-Type}}
on a [finite type](univalent-combinatorics.finite-types.md) is a
[measure](finite-probability-theory.measures-on-finite-types.md) with **total
measure** equal to 1.

## Definition

### The property of being a probability measure on a finite type

```agda
module _
  {l : Level} (Ω : Finite-Type l) (μ : measure-Finite-Type Ω)
  where

  is-probability-measure-prop-measure-Finite-Type : Prop (lsuc lzero)
  is-probability-measure-prop-measure-Finite-Type =
    Id-Prop
      ( ℝ-Set lzero)
      ( total-measure-Finite-Type Ω μ)
      ( one-ℝ)

  is-probability-measure-Finite-Type : UU (lsuc lzero)
  is-probability-measure-Finite-Type =
    type-Prop is-probability-measure-prop-measure-Finite-Type

  is-prop-is-probability-measure-Finite-Type :
    is-prop is-probability-measure-Finite-Type
  is-prop-is-probability-measure-Finite-Type =
    is-prop-type-Prop is-probability-measure-prop-measure-Finite-Type
```

### Probability measures on finite types

```agda
module _
  {l : Level} (Ω : Finite-Type l)
  where

  probability-measure-Finite-Type : UU (lsuc lzero ⊔ l)
  probability-measure-Finite-Type =
    type-subtype (is-probability-measure-prop-measure-Finite-Type Ω)
```
