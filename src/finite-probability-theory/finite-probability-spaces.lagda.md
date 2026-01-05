# Finite probability spaces

```agda
module finite-probability-theory.finite-probability-spaces where
```

<details><summary>Imports</summary>

```agda
open import finite-probability-theory.positive-distributions-on-finite-types
open import finite-probability-theory.probability-distributions-on-finite-types

open import foundation.coproduct-types
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

open import logic.propositional-double-negation-elimination

open import real-numbers.addition-real-numbers
open import real-numbers.apartness-real-numbers
open import real-numbers.dedekind-real-numbers
open import real-numbers.positive-real-numbers
open import real-numbers.rational-real-numbers
open import real-numbers.strict-inequality-real-numbers

open import univalent-combinatorics.finite-types
open import univalent-combinatorics.inhabited-finite-types
```

</details>

## Idea

A {{#concept "finite probability space" Agda=Finite-Probability-Space}} is a
[finite type](univalent-combinatorics.finite-types.md) equipped with a
[probability distribution](finite-probability-theory.probability-distributions-on-finite-types.md).

Any finite probability space is [inhabited](foundation.inhabited-types.md).

Our definitions follows {{#cite Babai00}}, except, there it is assumed that the
underlying type is [nonempty](foundation-core.empty-types.md), but this follows
from the condition of having
[total measure](finite-probability-theory.positive-distributions-on-finite-types.md)
equal to 1.

## Definitions

### Finite probability spaces

```agda
Finite-Probability-Space : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
Finite-Probability-Space l1 l2 =
  Σ ( Finite-Type l1)
    ( probability-distribution-Finite-Type l2)

module _
  {l1 l2 : Level} (Ω : Finite-Probability-Space l1 l2)
  where

  finite-type-Finite-Probability-Space : Finite-Type l1
  finite-type-Finite-Probability-Space = pr1 Ω

  type-Finite-Probability-Space : UU l1
  type-Finite-Probability-Space =
    type-Finite-Type finite-type-Finite-Probability-Space

  is-finite-type-Finite-Probability-Space :
    is-finite type-Finite-Probability-Space
  is-finite-type-Finite-Probability-Space =
    is-finite-type-Finite-Type finite-type-Finite-Probability-Space

  distribution-Finite-Probability-Space :
    positive-distribution-Finite-Type l2 finite-type-Finite-Probability-Space
  distribution-Finite-Probability-Space = pr1 (pr2 Ω)

  real-distribution-Finite-Probability-Space :
    type-Finite-Probability-Space → ℝ l2
  real-distribution-Finite-Probability-Space =
    real-positive-distribution-Finite-Type
      ( finite-type-Finite-Probability-Space)
      ( distribution-Finite-Probability-Space)

  eq-one-total-measure-distribution-Finite-Probability-Space :
    ( total-measure-positive-distribution-Finite-Type
      ( finite-type-Finite-Probability-Space)
      ( distribution-Finite-Probability-Space)) ＝
    ( raise-one-ℝ l2)
  eq-one-total-measure-distribution-Finite-Probability-Space = pr2 (pr2 Ω)
```

## Properties

### A finite probability space is nonempty

```agda
module _
  {l1 l2 : Level} (Ω : Finite-Probability-Space l1 l2)
  where

  is-nonempty-type-Finite-Probability-Space :
    is-nonempty (type-Finite-Probability-Space Ω)
  is-nonempty-type-Finite-Probability-Space H =
    neq-raise-zero-one-ℝ l2
      ( ( inv
          ( is-zero-total-measure-positive-distribution-is-empty-Finite-Type
            ( finite-type-Finite-Probability-Space Ω)
            ( distribution-Finite-Probability-Space Ω)
            ( H))) ∙
      ( eq-one-total-measure-distribution-Finite-Probability-Space Ω))
```

### A finite probability space is inhabited

```agda
module _
  {l1 l2 : Level} (Ω : Finite-Probability-Space l1 l2)
  where

  is-inhabited-type-Finite-Probability-Space :
    is-inhabited (type-Finite-Probability-Space Ω)
  is-inhabited-type-Finite-Probability-Space =
    prop-double-negation-elim-is-inhabited-or-empty
      ( is-inhabited-or-empty-is-finite
        ( is-finite-type-Finite-Probability-Space Ω))
      ( is-nonempty-type-Finite-Probability-Space Ω)

  inhabited-type-Finite-Probability-Space : Inhabited-Type l1
  inhabited-type-Finite-Probability-Space =
    ( type-Finite-Probability-Space Ω ,
      is-inhabited-type-Finite-Probability-Space)

  inhabited-finite-type-Finite-Probability-Space : Inhabited-Finite-Type l1
  inhabited-finite-type-Finite-Probability-Space =
    ( finite-type-Finite-Probability-Space Ω ,
      is-inhabited-type-Finite-Probability-Space)
```

## References

{{#bibliography}}
