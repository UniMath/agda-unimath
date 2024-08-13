# Apartness relation in metric spaces

```agda
module metric-spaces.apartness-relation-metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.positive-rational-numbers

open import foundation.empty-types
open import foundation.existential-quantification
open import foundation.negated-equality
open import foundation.negation
open import foundation.propositions
open import foundation.universe-levels

open import metric-spaces.metric-spaces
open import metric-spaces.neighbourhood-relations
```

</details>

## Idea

Two elements `x` and `y` in a [metric space](metric-spaces.md) are
{{#concept "apart" Disambiguation="in a metric space", Agda=apart-element-Metric-Space}}
if there [exists](foundation.existential-quantification.md) some `d : ℚ⁺` such
that `x` and `y` are not in a
[`d`-neighbourhood](metric-spaces.neighbourhood-relations.md).

## Definitions

```agda
module _
  {l : Level} (M : Metric-Space l) (x y : type-Metric-Space M)
  where

  apart-elements-prop-Metric-Space : Prop l
  apart-elements-prop-Metric-Space =
    ∃ ℚ⁺ (λ d → neg-Prop (neighbourhood-Metric-Space M d x y))

  apart-elements-Metric-Space : UU l
  apart-elements-Metric-Space = type-Prop apart-elements-prop-Metric-Space

  is-prop-apart-elements-Metric-Space :
    is-prop apart-elements-Metric-Space
  is-prop-apart-elements-Metric-Space =
    is-prop-type-Prop apart-elements-prop-Metric-Space
```

## Properties

### Two apart elements of a metric space are not equal

```agda
module _
  {l : Level} (M : Metric-Space l) (x y : type-Metric-Space M)
  where

  not-eq-apart-elements-Metric-Space :
    apart-elements-Metric-Space M x y → x ≠ y
  not-eq-apart-elements-Metric-Space H I =
    elim-exists
      ( empty-Prop)
      ( λ d J → J (indistinguishable-eq-Metric-Space M x y I d))
      ( H)
```
