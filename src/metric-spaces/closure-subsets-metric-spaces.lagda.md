# The closure of subsets of metric spaces

```agda
module metric-spaces.closure-subsets-metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.positive-rational-numbers

open import foundation.dependent-pair-types
open import foundation.empty-subtypes
open import foundation.empty-types
open import foundation.intersections-subtypes
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.raising-universe-levels
open import foundation.subtypes
open import foundation.universe-levels

open import metric-spaces.metric-spaces
open import metric-spaces.subspaces-metric-spaces
```

</details>

## Idea

A
{{#concept "limit point" disambiguation="of a subset of a metric space" WDID=Q858223 WD="limit point" Agda=is-limit-point-subset-Metric-Space}}
of a [subset](foundation.subtypes.md) `S` of a
[metric space](metric-spaces.metric-spaces.md) `X` is a point `x` of `X` where
every neighborhood of `x` [intersects](foundation.intersections-subtypes.md)
`S`.

The
{{#concept "closure" disambiguation="of a subset of a metric space" WDID=Q320346 WD="closure" Agda=closure-subset-Metric-Space}}
of `S` is the set of limit points of `S`.

## Definition

```agda
module _
  {l1 l2 l3 : Level} (X : Metric-Space l1 l2) (S : subset-Metric-Space l3 X)
  where

  closure-subset-Metric-Space : subset-Metric-Space (l1 ⊔ l2 ⊔ l3) X
  closure-subset-Metric-Space x =
    Π-Prop
      ( ℚ⁺)
      ( λ ε → intersect-prop-subtype (neighborhood-prop-Metric-Space X ε x) S)

  is-limit-point-subset-Metric-Space : type-Metric-Space X → UU (l1 ⊔ l2 ⊔ l3)
  is-limit-point-subset-Metric-Space =
    is-in-subtype closure-subset-Metric-Space
```

## Properties

### The closure of the empty set is empty

```agda
module _
  {l1 l2 : Level} (X : Metric-Space l1 l2)
  where

  is-empty-closure-empty-subset-Metric-Space :
    is-empty-subtype
      ( closure-subset-Metric-Space X (empty-subset-Metric-Space X))
  is-empty-closure-empty-subset-Metric-Space x x∈closure-∅ =
    let open do-syntax-trunc-Prop empty-Prop
    in do
      (s , s∈N1x , s∈∅) ← x∈closure-∅ one-ℚ⁺
      map-inv-raise s∈∅
```
