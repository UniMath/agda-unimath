# Approximations in located metric spaces

```agda
module metric-spaces.approximations-located-metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.positive-rational-numbers

open import foundation.dependent-pair-types
open import foundation.full-subtypes
open import foundation.propositions
open import foundation.subtypes
open import foundation.unions-subtypes
open import foundation.universe-levels

open import metric-spaces.approximations-metric-spaces
open import metric-spaces.located-metric-spaces
open import metric-spaces.metric-spaces
open import metric-spaces.subspaces-metric-spaces
```

</details>

## Idea

For an `ε : ℚ⁺`, an
`ε`-{{#concept "approximation" disambiguation="of a located metric space" Agda=approximation-Located-Metric-Space}}
of a [located metric space](metric-spaces.located-metric-spaces.md) `X` is an
[`ε`-approximation](metric-spaces.approximations-metric-spaces.md) in the
corresponding [metric space](metric-spaces.metric-spaces.md)

## Definition

```agda
module _
  {l1 l2 l3 : Level} (X : Located-Metric-Space l1 l2) (ε : ℚ⁺)
  (S : subset-Located-Metric-Space l3 X)
  where

  is-approximation-prop-Located-Metric-Space : Prop (l1 ⊔ l2 ⊔ l3)
  is-approximation-prop-Located-Metric-Space =
    is-approximation-prop-Metric-Space
      ( metric-space-Located-Metric-Space X)
      ( ε)
      ( S)

  is-approximation-Located-Metric-Space : UU (l1 ⊔ l2 ⊔ l3)
  is-approximation-Located-Metric-Space =
    type-Prop is-approximation-prop-Located-Metric-Space

approximation-Located-Metric-Space :
  {l1 l2 : Level} (l3 : Level) (X : Located-Metric-Space l1 l2) (ε : ℚ⁺) →
  UU (l1 ⊔ l2 ⊔ lsuc l3)
approximation-Located-Metric-Space l3 X =
  approximation-Metric-Space l3 (metric-space-Located-Metric-Space X)

module _
  {l1 l2 l3 : Level} (X : Located-Metric-Space l1 l2) (ε : ℚ⁺)
  (S : approximation-Located-Metric-Space l3 X ε)
  where

  subset-approximation-Located-Metric-Space : subset-Located-Metric-Space l3 X
  subset-approximation-Located-Metric-Space = pr1 S

  type-approximation-Located-Metric-Space : UU (l1 ⊔ l3)
  type-approximation-Located-Metric-Space =
    type-subtype subset-approximation-Located-Metric-Space
```
