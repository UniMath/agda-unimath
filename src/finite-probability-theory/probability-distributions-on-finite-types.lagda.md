# Probability distributions on finite types

```agda
module finite-probability-theory.probability-distributions-on-finite-types where
```

<details><summary>Imports</summary>

```agda
open import finite-probability-theory.positive-distributions-on-finite-types

open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.function-types
open import foundation.identity-types
open import foundation.inhabited-types
open import foundation.propositions
open import foundation.sets
open import foundation.universe-levels

open import ring-theory.large-rings
open import ring-theory.rings

open import real-numbers.addition-real-numbers
open import real-numbers.dedekind-real-numbers
open import real-numbers.large-ring-of-real-numbers
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
  {l1 l2 : Level} (Ω : Finite-Type l1)
  (Pr : positive-distribution-Finite-Type l2 Ω)
  where

  is-probability-distribution-prop-positive-distribution-Finite-Type :
    Prop (lsuc l2)
  is-probability-distribution-prop-positive-distribution-Finite-Type =
    Id-Prop
      ( ℝ-Set l2)
      ( total-measure-positive-distribution-Finite-Type Ω Pr)
      ( one-ring-ℝ l2)

  is-probability-distribution-positive-distribution-Finite-Type :
    UU (lsuc l2)
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
  {l1 : Level} (l2 : Level) (Ω : Finite-Type l1)
  where

  probability-distribution-Finite-Type : UU (l1 ⊔ lsuc l2)
  probability-distribution-Finite-Type =
    Σ ( positive-distribution-Finite-Type l2 Ω)
      ( is-probability-distribution-positive-distribution-Finite-Type Ω)
```
