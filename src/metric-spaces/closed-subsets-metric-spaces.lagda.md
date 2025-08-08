# Closed subsets of metric spaces

```agda
module metric-spaces.closed-subsets-metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.positive-rational-numbers

open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.raising-universe-levels
open import foundation.sets
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.unit-type
open import foundation.universe-levels

open import metric-spaces.closure-subsets-metric-spaces
open import metric-spaces.dense-subsets-metric-spaces
open import metric-spaces.discrete-metric-spaces
open import metric-spaces.metric-spaces
open import metric-spaces.subspaces-metric-spaces
```

</details>

## Idea

A [subset](foundation.subtypes.md) `S` of a
[metric space](metric-spaces.metric-spaces.md) `X` is
{{#concept "closed" disambiguation="subset of a metric space" WDID=Q320357 WD="closed set" Agda=is-closed-subset-Metric-Space}}
if its [closure](metric-spaces.closure-subsets-metric-spaces.md) is a subset of
`S`.

## Definition

```agda
module _
  {l1 l2 l3 : Level} (X : Metric-Space l1 l2) (S : subset-Metric-Space l3 X)
  where

  is-closed-prop-subset-Metric-Space : Prop (l1 ⊔ l2 ⊔ l3)
  is-closed-prop-subset-Metric-Space =
    leq-prop-subtype (closure-subset-Metric-Space X S) S

  is-closed-subset-Metric-Space : UU (l1 ⊔ l2 ⊔ l3)
  is-closed-subset-Metric-Space = type-Prop is-closed-prop-subset-Metric-Space
```

## Properties

### The empty set is closed

```agda
module _
  {l1 l2 : Level} (X : Metric-Space l1 l2)
  where

  is-closed-empty-subset-Metric-Space :
    is-closed-subset-Metric-Space X (empty-subset-Metric-Space X)
  is-closed-empty-subset-Metric-Space x x∈closure =
    map-raise (is-empty-closure-empty-subset-Metric-Space X x x∈closure)
```

### A metric space is closed in itself

```agda
  is-closed-full-subset-Metric-Space :
    is-closed-subset-Metric-Space X (full-subset-Metric-Space X)
  is-closed-full-subset-Metric-Space x _ = map-raise star
```

### Every subset of a discrete metric space is closed

```agda
module _
  {l1 l2 l3 : Level} (X : Discrete-Metric-Space l1 l2)
  where

  is-closed-subset-Discrete-Metric-Space :
    (S : subtype l3 (type-Discrete-Metric-Space X)) →
    is-closed-subset-Metric-Space
      ( metric-space-Discrete-Metric-Space X)
      ( S)
  is-closed-subset-Discrete-Metric-Space S x x∈closure =
    let open do-syntax-trunc-Prop (S x)
    in do
      (y , y∈N1x , y∈S) ← x∈closure one-ℚ⁺
      inv-tr
        ( type-Prop ∘ S)
        ( is-discrete-metric-space-Discrete-Metric-Space X one-ℚ⁺ x y y∈N1x)
        ( y∈S)
```
