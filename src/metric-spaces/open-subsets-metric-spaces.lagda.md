# Open subsets of metric spaces

```agda
module metric-spaces.open-subsets-metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.minimum-rational-numbers
open import elementary-number-theory.positive-rational-numbers

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
open import foundation.universe-levels

open import metric-spaces.discrete-metric-spaces
open import metric-spaces.interior-subsets-metric-spaces
open import metric-spaces.metric-spaces
open import metric-spaces.subspaces-metric-spaces
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

  is-open-subset-open-subset-Metric-Space :
    (O : open-subset-Metric-Space l3 X) →
    is-open-subset-Metric-Space X (subset-open-subset-Metric-Space O)
  is-open-subset-open-subset-Metric-Space = pr2
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
      ( one-ℚ⁺)
      ( λ y N1xy →
        tr
          ( type-Prop ∘ S)
          ( is-discrete-metric-space-Discrete-Metric-Space X one-ℚ⁺ x y N1xy)
          ( x∈S))
```

### The intersection of two open subsets is open

```agda
module _
  {l1 l2 l3 l4 : Level} (X : Metric-Space l1 l2)
  (S : open-subset-Metric-Space l3 X) (T : open-subset-Metric-Space l4 X)
  where

  subset-intersection-open-subset-Metric-Space :
    subset-Metric-Space (l3 ⊔ l4) X
  subset-intersection-open-subset-Metric-Space =
    intersection-subtype
      ( subset-open-subset-Metric-Space X S)
      ( subset-open-subset-Metric-Space X T)

  is-open-subset-intersection-open-subset-Metric-Space :
    is-open-subset-Metric-Space
      ( X)
      ( subset-intersection-open-subset-Metric-Space)
  is-open-subset-intersection-open-subset-Metric-Space x (x∈S , x∈T) =
    let
      open
        do-syntax-trunc-Prop
          ( interior-subset-Metric-Space
            ( X)
            ( subset-intersection-open-subset-Metric-Space)
            ( x))
    in do
      (εS , NεSx⊆S) ←
        is-open-subset-open-subset-Metric-Space X S x x∈S
      (εT , NεTx⊆T) ←
        is-open-subset-open-subset-Metric-Space X T x x∈T
      let εmin = min-ℚ⁺ εS εT
      intro-exists
        ( εmin)
        ( λ y y∈Nεminx →
          ( NεSx⊆S
            ( y)
            ( weakly-monotonic-neighborhood-Metric-Space X x y
              ( εmin)
              ( εS)
              ( leq-left-min-ℚ⁺ εS εT)
              ( y∈Nεminx)) ,
            NεTx⊆T
              ( y)
              ( weakly-monotonic-neighborhood-Metric-Space X x y
                ( εmin)
                ( εT)
                ( leq-right-min-ℚ⁺ εS εT)
                ( y∈Nεminx))))
```
