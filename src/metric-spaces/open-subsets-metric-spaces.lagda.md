# Open subsets of metric spaces

```agda
module metric-spaces.open-subsets-metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.positive-rational-numbers

open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.existential-quantification
open import foundation.function-types
open import foundation.transport-along-identifications
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.raising-universe-levels
open import foundation.subtypes
open import foundation.universe-levels


open import metric-spaces.metric-spaces
open import metric-spaces.subspaces-metric-spaces
open import metric-spaces.interior-subsets-metric-spaces
open import metric-spaces.discrete-metric-spaces
```

</details>

## Idea

A [subset](foundation.subtypes.md) `S` of a
[metric space](metric-spaces.metric-spaces.md) `X` is
{{#concept "open" disambiguation="in a metric space" WDID=Q213363 WD="open set" Agda=is-open-subset-Metric-Space}}
if it is a subset of its
[interior](metric-spaces.interior-subsets-metric-spaces.md).

## Definition

```agda
module _
  {l1 l2 l3 : Level} (X : Metric-Space l1 l2) (S : subset-Metric-Space l3 X)
  where

  is-open-subset-prop-Metric-Space : Prop (l1 ⊔ l2 ⊔ l3)
  is-open-subset-prop-Metric-Space =
    leq-prop-subtype S (interior-subset-Metric-Space X S)

  is-open-subset-Metric-Space : UU (l1 ⊔ l2 ⊔ l3)
  is-open-subset-Metric-Space = type-Prop is-open-subset-prop-Metric-Space

open-subset-Metric-Space :
  {l1 l2 : Level} (l3 : Level) (X : Metric-Space l1 l2) → UU (l1 ⊔ l2 ⊔ lsuc l3)
open-subset-Metric-Space l3 X =
  type-subtype (is-open-subset-prop-Metric-Space {l3 = l3} X)

module _
  {l1 l2 l3 : Level} (X : Metric-Space l1 l2)
  where

  subset-open-subset-Metric-Space :
    open-subset-Metric-Space l3 X → subset-Metric-Space l3 X
  subset-open-subset-Metric-Space = pr1
```

## Properties

### The empty subset is open

```agda
module _
  {l1 l2 : Level} (X : Metric-Space l1 l2)
  where

  is-open-empty-subset-Metric-Space :
    is-open-subset-Metric-Space X (empty-subset-Metric-Space X)
  is-open-empty-subset-Metric-Space x (map-raise ⊥) = ex-falso ⊥
```

### The full subset is open

```agda
module _
  {l1 l2 : Level} (X : Metric-Space l1 l2)
  where

  is-open-full-subset-Metric-Space :
    is-open-subset-Metric-Space X (full-subset-Metric-Space X)
  is-open-full-subset-Metric-Space x _ =
    is-full-interior-full-subset-Metric-Space X x
```

### Every subset of a discrete metric space is open

```agda
module _
  {l1 l2 : Level} (X : Discrete-Metric-Space l1 l2)
  where

  is-open-subset-Discrete-Metric-Space :
    {l3 : Level} (S : subtype l3 (type-Discrete-Metric-Space X)) →
    is-open-subset-Metric-Space
      ( metric-space-Discrete-Metric-Space X)
      ( S)
  is-open-subset-Discrete-Metric-Space S x x∈S =
    intro-exists
      ( one-ℚ⁺ )
      ( λ y N1xy →
        tr
          ( type-Prop ∘ S)
          ( is-discrete-metric-space-Discrete-Metric-Space X one-ℚ⁺ x y N1xy)
          ( x∈S))
```
