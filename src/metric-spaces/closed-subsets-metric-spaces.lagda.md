# Closed subsets of metric spaces

```agda
module metric-spaces.closed-subsets-metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.empty-subtypes
open import foundation.empty-types
open import foundation.intersections-subtypes
open import foundation.propositions
open import foundation.raising-universe-levels
open import foundation.sets
open import foundation.subtypes
open import foundation.unit-type
open import foundation.universe-levels

open import metric-spaces.closure-subsets-metric-spaces
open import metric-spaces.dense-subsets-metric-spaces
open import metric-spaces.metric-spaces
open import metric-spaces.subspaces-metric-spaces
```

</details>

## Idea

A [subset](foundation.subtypes.md) `S` of a
[metric space](metric-spaces.metric-spaces.md) `X` is
{{#concept "closed" disambiguation="subset of a metric space" WDID=Q320357 WD="closed set" Agda=is-closed-subset-Metric-Space}}
if its [closure](metric-spaces.closure-subsets-metric-spaces.md) is itself.

## Definition

```agda
module _
  {l1 l2 l3 : Level} (X : Metric-Space l1 l2) (S : subset-Metric-Space l3 X)
  where

  is-closed-prop-subset-Metric-Space : Prop (l1 ⊔ l2 ⊔ l3)
  is-closed-prop-subset-Metric-Space =
    has-same-elements-subtype-Prop (closure-subset-Metric-Space X S) S

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
  pr1 (is-closed-empty-subset-Metric-Space x) x∈closure =
    map-raise (is-empty-closure-empty-subset-Metric-Space X x x∈closure)
  pr2 (is-closed-empty-subset-Metric-Space x) (map-raise ⊥) = ex-falso ⊥
```

### A metric space is closed in itself

```agda
  is-closed-full-subset-Metric-Space :
    is-closed-subset-Metric-Space X (full-subset-Metric-Space X)
  pr1 (is-closed-full-subset-Metric-Space x) x∈closure = map-raise star
  pr2 (is-closed-full-subset-Metric-Space x) _ =
    is-dense-full-subset-Metric-Space X x
```
