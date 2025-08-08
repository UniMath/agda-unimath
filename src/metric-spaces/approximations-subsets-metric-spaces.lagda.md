# Approximations of subsets of metric spaces

```agda
module metric-spaces.approximations-subsets-metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.positive-rational-numbers

open import foundation.dependent-pair-types
open import foundation.propositions
open import foundation.subtypes
open import foundation.unions-subtypes
open import foundation.universe-levels

open import metric-spaces.metric-spaces
open import metric-spaces.subspaces-metric-spaces
```

</details>

## Idea

For an `ε : ℚ⁺`, a [metric space](metric-spaces.metric-spaces.md) `X`, and a
[subset](foundation.subtypes.md) `S` of `X`, an
{{#concept "ε-approximation" disambiguation="in a metric space"}} of `S` is a
subset `T ⊆ S` such that `S` is a subset of the
[union](foundation.union-subtypes.md) of `ε`-neighborhoods of elements of `T`.

## Definitions

```agda
module _
  {l1 l2 l3 : Level}
  (X : Metric-Space l1 l2) (S : subset-Metric-Space l3 X) (ε : ℚ⁺)
  {l4 : Level} (T : subtype l4 (type-subtype S))
  where

  is-approximation-prop-subset-Metric-Space : Prop (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  is-approximation-prop-subset-Metric-Space =
    leq-prop-subtype
      ( S)
      ( union-family-of-subtypes
        { I = type-subtype T}
        ( λ ((t , t∈S) , t∈T) → neighborhood-prop-Metric-Space X ε t))

  is-approximation-subset-Metric-Space : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  is-approximation-subset-Metric-Space =
    type-Prop is-approximation-prop-subset-Metric-Space

module _
  {l1 l2 l3 : Level}
  (X : Metric-Space l1 l2) (S : subset-Metric-Space l3 X) (ε : ℚ⁺)
  (l4 : Level)
  where

  approximation-subset-Metric-Space : UU (l1 ⊔ l2 ⊔ l3 ⊔ lsuc l4)
  approximation-subset-Metric-Space =
    type-subtype (is-approximation-prop-subset-Metric-Space X S ε {l4})

  subtype-approximation-subset-Metric-Space :
    approximation-subset-Metric-Space → subtype l4 (type-subtype S)
  subtype-approximation-subset-Metric-Space = pr1

  is-approximation-approximation-subset-Metric-Space :
    (T : approximation-subset-Metric-Space) →
    is-approximation-subset-Metric-Space X S ε
      ( subtype-approximation-subset-Metric-Space T)
  is-approximation-approximation-subset-Metric-Space = pr2
```
