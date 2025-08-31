# Open subsets of located metric spaces

```agda
module metric-spaces.open-subsets-located-metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.minimum-rational-numbers
open import elementary-number-theory.positive-rational-numbers

open import foundation.cartesian-products-subtypes
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.existential-quantification
open import foundation.function-types
open import foundation.intersections-subtypes
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.raising-universe-levels
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.unions-subtypes
open import foundation.universe-levels

open import metric-spaces.cartesian-products-metric-spaces
open import metric-spaces.discrete-metric-spaces
open import metric-spaces.interior-subsets-metric-spaces
open import metric-spaces.located-metric-spaces
open import metric-spaces.metric-spaces
open import metric-spaces.open-subsets-metric-spaces
open import metric-spaces.subspaces-metric-spaces
```

</details>

## Idea

A [subset](foundation.subtypes.md) `S` of a
[located metric space](metric-spaces.located-metric-spaces.md) `X` is
{{#concept "open" disambiguation="in a located metric space" WDID=Q213363 WD="open set" Agda=is-open-subset-Located-Metric-Space}}
if it is an [open subset](metric-spaces.open-subsets-metric-spaces.md) of the
corresponding [metric space](metric-spaces.metric-spaces.md).

## Definition

```agda
module _
  {l1 l2 l3 : Level}
  (X : Located-Metric-Space l1 l2) (S : subset-Located-Metric-Space l3 X)
  where

  is-open-prop-subset-Located-Metric-Space : Prop (l1 ⊔ l2 ⊔ l3)
  is-open-prop-subset-Located-Metric-Space =
    is-open-prop-subset-Metric-Space
      ( metric-space-Located-Metric-Space X)
      ( S)

  is-open-subset-Located-Metric-Space : UU (l1 ⊔ l2 ⊔ l3)
  is-open-subset-Located-Metric-Space =
    type-Prop is-open-prop-subset-Located-Metric-Space

open-subset-Located-Metric-Space :
  {l1 l2 : Level} (l3 : Level)
  (X : Located-Metric-Space l1 l2) → UU (l1 ⊔ l2 ⊔ lsuc l3)
open-subset-Located-Metric-Space l3 X =
  open-subset-Metric-Space l3 (metric-space-Located-Metric-Space X)

module _
  {l1 l2 l3 : Level} (X : Located-Metric-Space l1 l2)
  (S : open-subset-Located-Metric-Space l3 X)
  where

  subset-open-subset-Located-Metric-Space : subset-Located-Metric-Space l3 X
  subset-open-subset-Located-Metric-Space = pr1 S

  is-open-subset-open-subset-Located-Metric-Space :
    is-open-subset-Located-Metric-Space
      ( X)
      ( subset-open-subset-Located-Metric-Space)
  is-open-subset-open-subset-Located-Metric-Space = pr2 S
```
