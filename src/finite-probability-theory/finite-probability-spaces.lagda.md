# Finite probability spaces

```agda
module finite-probability-theory.finite-probability-spaces where
```

<details><summary>Imports</summary>

```agda
open import finite-probability-theory.positive-distributions-on-finite-types
open import finite-probability-theory.probability-distributions-on-finite-types

open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.function-types
open import foundation.identity-types
open import foundation.inhabited-types
open import foundation.propositions
open import foundation.sets
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import group-theory.sums-of-finite-families-of-elements-abelian-groups

open import real-numbers.addition-real-numbers
open import real-numbers.dedekind-real-numbers
open import real-numbers.positive-real-numbers
open import real-numbers.rational-real-numbers
open import real-numbers.strict-inequality-real-numbers

open import univalent-combinatorics.finite-types
```

</details>

## Idea

A {{#concept "finite probability space" Agda=Finite-Probability-Space}} is a
[finite type](univalent-combinatorics.finite-types.md) equipped with a
[probability distribution](finite-probability-theory.probability-distributions-on-finite-types.md).

Our definitions follows {{#cite Babai00}} but the
[non-emptiness](foundation-core.empty-types.md) of the underlying type is
actually a consequence of the condition of having
[total measure](finite-probability-theory.positive-distributions-on-finite-types.md)
equal to 1.

## Definitions

### Finite probability spaces

```agda
Finite-Probability-Space : (l : Level) → UU (lsuc l)
Finite-Probability-Space l =
  Σ ( Finite-Type l)
    ( probability-distribution-Finite-Type)

module _
  {l : Level} (Ω : Finite-Probability-Space l)
  where

  finite-type-Finite-Probability-Space : Finite-Type l
  finite-type-Finite-Probability-Space = pr1 Ω

  type-Finite-Probability-Space : UU l
  type-Finite-Probability-Space =
    type-Finite-Type finite-type-Finite-Probability-Space

  is-finite-type-Finite-Probability-Space :
    is-finite type-Finite-Probability-Space
  is-finite-type-Finite-Probability-Space =
    is-finite-type-Finite-Type finite-type-Finite-Probability-Space

  distribution-Finite-Probability-Space :
    positive-distribution-Finite-Type finite-type-Finite-Probability-Space
  distribution-Finite-Probability-Space = pr1 (pr2 Ω)

  real-distribution-Finite-Probability-Space :
    type-Finite-Probability-Space → ℝ lzero
  real-distribution-Finite-Probability-Space =
    real-positive-distribution-Finite-Type
      ( finite-type-Finite-Probability-Space)
      ( distribution-Finite-Probability-Space)

  eq-one-total-measure-distribution-Finite-Probability-Space :
    ( total-measure-positive-distribution-Finite-Type
      ( finite-type-Finite-Probability-Space)
      ( distribution-Finite-Probability-Space)) ＝
    one-ℝ
  eq-one-total-measure-distribution-Finite-Probability-Space =
    pr2 (pr2 (Ω))
```

## Properties

### A finite probability space is nonempty

```agda
module _
  {l : Level} (Ω : Finite-Probability-Space l)
  where

  is-nonempty-type-Finite-Probability-Space :
    is-nonempty (type-Finite-Probability-Space Ω)
  is-nonempty-type-Finite-Probability-Space =
    not-0＝1 ∘ absurd-is-empty-Finite-Probability-Space
    where

    absurd-is-empty-Finite-Probability-Space :
      is-empty (type-Finite-Probability-Space Ω) →
      zero-ℝ ＝ one-ℝ
    absurd-is-empty-Finite-Probability-Space H =
      ( inv
        ( is-zero-total-measure-positive-distribution-is-empty-Finite-Type
          ( finite-type-Finite-Probability-Space Ω)
          ( distribution-Finite-Probability-Space Ω)
          ( H))) ∙
      ( eq-one-total-measure-distribution-Finite-Probability-Space Ω)

    not-0＝1 : is-empty (zero-ℝ ＝ one-ℝ)
    not-0＝1 H =
      irreflexive-le-ℝ
        ( zero-ℝ)
        ( inv-tr
          ( le-ℝ zero-ℝ)
          ( H)
          ( is-positive-real-ℝ⁺ one-ℝ⁺))
```
