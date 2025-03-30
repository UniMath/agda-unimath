# Uniformly continuous binary functions between metric spaces

```agda
module metric-spaces.uniformly-continuous-binary-functions-metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.positive-rational-numbers

open import foundation.function-types
open import foundation.propositions
open import foundation.dependent-pair-types
open import foundation.universe-levels
open import foundation.cartesian-product-types

open import metric-spaces.continuous-functions-metric-spaces
open import metric-spaces.functions-metric-spaces
open import metric-spaces.products-metric-spaces
open import metric-spaces.metric-spaces
open import metric-spaces.uniformly-continuous-functions-metric-spaces
open import metric-spaces.short-functions-metric-spaces
```

</details>

## Idea

A [binary function](metric-spaces.functions-metric-spaces.md) `f` from
[metric spaces](metric-spaces.metric-spaces.md) `X` and `Y` to `Z` is
{{#concept "uniformly continuous" Disambiguation="binary function between metric spaces" WDID=Q741865 WD="uniform continuity" Agda=is-uniformly-continuous-binary-map-Metric-Space}}
if the induced map `ind-product f : X × Y → Z` is a uniformly
continuous map from the
[product metric space](metric-spaces.products-metric-spaces.md) of `X` and `Y`
to `Z`.

## Definitions

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  (X : Metric-Space l1 l2) (Y : Metric-Space l3 l4) (Z : Metric-Space l5 l6)
  (f : binary-map-type-Metric-Space X Y Z)
  where

  is-uniformly-continuous-binary-map-prop-Metric-Space :
    Prop (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l6)
  is-uniformly-continuous-binary-map-prop-Metric-Space =
    is-uniformly-continuous-map-prop-Metric-Space
      ( product-Metric-Space X Y)
      ( Z)
      ( ind-product f)

  is-uniformly-continuous-binary-map-Metric-Space : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l6)
  is-uniformly-continuous-binary-map-Metric-Space =
    type-Prop is-uniformly-continuous-binary-map-prop-Metric-Space
```

## Properties

### The projection maps are uniformly continuous

```agda
module _
  {l1 l2 l3 l4 : Level}
  (X : Metric-Space l1 l2) (Y : Metric-Space l3 l4)
  where

  abstract
    is-uniformly-continuous-first-map-Metric-Space :
      is-uniformly-continuous-binary-map-Metric-Space X Y X (λ a b → a)
    is-uniformly-continuous-first-map-Metric-Space =
      is-uniformly-continuous-is-short-function-Metric-Space
        ( product-Metric-Space X Y)
        ( X)
        ( pr1)
        ( is-short-pr1-product-Metric-Space X Y)

    is-uniformly-continuous-second-map-Metric-Space :
      is-uniformly-continuous-binary-map-Metric-Space X Y Y (λ a b → b)
    is-uniformly-continuous-second-map-Metric-Space =
      is-uniformly-continuous-is-short-function-Metric-Space
        ( product-Metric-Space X Y)
        ( Y)
        ( pr2)
        ( is-short-pr2-product-Metric-Space X Y)
```
