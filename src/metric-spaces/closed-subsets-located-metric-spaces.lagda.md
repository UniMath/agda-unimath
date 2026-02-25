# Closed subsets of located metric spaces

```agda
module metric-spaces.closed-subsets-located-metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.propositions
open import foundation.subtypes
open import foundation.universe-levels

open import metric-spaces.closed-subsets-metric-spaces
open import metric-spaces.located-metric-spaces
open import metric-spaces.metric-spaces
```

</details>

## Idea

A [subset](foundation.subtypes.md) `S` of a
[located metric space](metric-spaces.located-metric-spaces.md) `X` is
{{#concept "closed" disambiguation="subset of a located metric space" WDID=Q320357 WD="closed set" Agda=is-closed-subset-Located-Metric-Space}}
if it is a [closed subset](metric-spaces.closed-subsets-metric-spaces.md) of the
underlying [metric space](metric-spaces.metric-spaces.md)

## Definition

```agda
module _
  {l1 l2 l3 : Level}
  (X : Located-Metric-Space l1 l2) (S : subset-Located-Metric-Space l3 X)
  where

  is-closed-prop-subset-Located-Metric-Space : Prop (l1 ⊔ l2 ⊔ l3)
  is-closed-prop-subset-Located-Metric-Space =
    is-closed-prop-subset-Metric-Space
      ( metric-space-Located-Metric-Space X)
      ( S)

  is-closed-subset-Located-Metric-Space : UU (l1 ⊔ l2 ⊔ l3)
  is-closed-subset-Located-Metric-Space =
    type-Prop is-closed-prop-subset-Located-Metric-Space

closed-subset-Located-Metric-Space :
  {l1 l2 : Level} (l3 : Level)
  (X : Located-Metric-Space l1 l2) → UU (l1 ⊔ l2 ⊔ lsuc l3)
closed-subset-Located-Metric-Space l3 X =
  closed-subset-Metric-Space l3 (metric-space-Located-Metric-Space X)

subset-closed-subset-Located-Metric-Space :
  {l1 l2 l3 : Level} (X : Located-Metric-Space l1 l2) →
  (S : closed-subset-Located-Metric-Space l3 X) →
  subset-Located-Metric-Space l3 X
subset-closed-subset-Located-Metric-Space X = pr1

is-closed-subset-closed-subset-Located-Metric-Space :
  {l1 l2 l3 : Level} (X : Located-Metric-Space l1 l2) →
  (S : closed-subset-Located-Metric-Space l3 X) →
  is-closed-subset-Located-Metric-Space
    ( X)
    ( subset-closed-subset-Located-Metric-Space X S)
is-closed-subset-closed-subset-Located-Metric-Space X = pr2

is-in-closed-subset-Located-Metric-Space :
  {l1 l2 l3 : Level} (X : Located-Metric-Space l1 l2) →
  (S : closed-subset-Located-Metric-Space l3 X) →
  type-Located-Metric-Space X → UU l3
is-in-closed-subset-Located-Metric-Space X S = is-in-subtype (pr1 S)
```
