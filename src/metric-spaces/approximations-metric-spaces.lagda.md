# Approximations in metric spaces

```agda
module metric-spaces.approximations-metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.positive-rational-numbers
open import foundation.dependent-pair-types
open import foundation.universe-levels
open import foundation.subtypes
open import metric-spaces.subspaces-metric-spaces
open import foundation.propositions
open import foundation.full-subtypes
open import foundation.unions-subtypes
open import metric-spaces.metric-spaces
open import metric-spaces.located-metric-spaces
```

</details>

## Idea

For an `ε : ℚ⁺`, an
`ε`-{{#concept "approximation" disambiguation="of a metric space"}} of a
[metric space](metric-spaces.metric-spaces.md) `X` is a
[subset](foundation.subtypes.md) `S` of `X` such that every point in `X` is
in an `ε`-neighborhood of some `s ∈ S`.

This terminology is taken from {{#cite BV06}} section 2.2.

A finite `ε`-approximation is called an
[`ε`-net](metric-spaces.nets-metric-spaces.md).

## Definition

```agda
module _
  {l1 l2 l3 : Level} (X : Metric-Space l1 l2) (ε : ℚ⁺)
  (S : subset-Metric-Space l3 X)
  where

  is-approximation-prop-Metric-Space : Prop (l1 ⊔ l2 ⊔ l3)
  is-approximation-prop-Metric-Space =
    is-full-subtype-Prop
      ( union-family-of-subtypes
        { I = type-subtype S}
        ( λ (s , s∈S) → neighborhood-prop-Metric-Space X ε s))

  is-approximation-Metric-Space : UU (l1 ⊔ l2 ⊔ l3)
  is-approximation-Metric-Space =
    type-Prop is-approximation-prop-Metric-Space

approximation-Metric-Space :
  {l1 l2 : Level} (l3 : Level) (X : Metric-Space l1 l2) (ε : ℚ⁺) →
  UU (l1 ⊔ l2 ⊔ lsuc l3)
approximation-Metric-Space l3 X ε =
  type-subtype (is-approximation-prop-Metric-Space {l3 = l3} X ε)

module _
  {l1 l2 l3 : Level} (X : Metric-Space l1 l2) (ε : ℚ⁺)
  (S : approximation-Metric-Space l3 X ε)
  where

  subset-approximation-Metric-Space : subset-Metric-Space l3 X
  subset-approximation-Metric-Space = pr1 S

  type-approximation-Metric-Space : UU (l1 ⊔ l3)
  type-approximation-Metric-Space =
    type-subtype subset-approximation-Metric-Space
```

### In a located metric space

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

## References

{{#bibliography}}
