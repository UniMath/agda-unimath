# Dense subsets of metric spaces

```agda
module metric-spaces.dense-subsets-metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.positive-rational-numbers

open import foundation.dependent-pair-types
open import foundation.existential-quantification
open import foundation.full-subtypes
open import foundation.propositions
open import foundation.raising-universe-levels
open import foundation.subtypes
open import foundation.unit-type
open import foundation.universe-levels

open import metric-spaces.closure-subsets-metric-spaces
open import metric-spaces.metric-spaces
open import metric-spaces.subspaces-metric-spaces
```

</details>

## Idea

A [subset](foundation.subtypes.md) `S` of a
[metric space](metric-spaces.metric-spaces.md) is
{{#concept "dense" disambiguation="in a metric space" WDID=Q673444 WD="dense set" Agda=is-dense-subset-Metric-Space}}
if its [closure](metric-spaces.closure-subsets-metric-spaces.md) is
[full](foundation.full-subtypes.md).

## Definition

```agda
module _
  {l1 l2 l3 : Level} (X : Metric-Space l1 l2) (S : subset-Metric-Space l3 X)
  where

  is-dense-prop-subset-Metric-Space : Prop (l1 ⊔ l2 ⊔ l3)
  is-dense-prop-subset-Metric-Space =
    is-full-subtype-Prop (closure-subset-Metric-Space X S)

  is-dense-subset-Metric-Space : UU (l1 ⊔ l2 ⊔ l3)
  is-dense-subset-Metric-Space = type-Prop is-dense-prop-subset-Metric-Space
```

## Properties

### A metric space is dense in itself

```agda
module _
  {l1 l2 : Level} (X : Metric-Space l1 l2)
  where

  is-dense-full-subset-Metric-Space :
    is-dense-subset-Metric-Space X (full-subset-Metric-Space X)
  is-dense-full-subset-Metric-Space x ε =
    intro-exists x (refl-neighborhood-Metric-Space X ε x , map-raise star)
```
