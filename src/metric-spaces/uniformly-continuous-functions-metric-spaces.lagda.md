# Uniformly continuous functions between metric spaces

```agda
module metric-spaces.uniformly-continuous-functions-metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.positive-rational-numbers

open import foundation.function-types
open import foundation.propositions
open import foundation.subtypes
open import foundation.universe-levels

open import metric-spaces.continuous-functions-metric-spaces
open import metric-spaces.functions-metric-spaces
open import metric-spaces.metric-spaces
open import metric-spaces.uniformly-continuous-functions-premetric-spaces
```

</details>

## Idea

A [function](metric-spaces.functions-metric-spaces.md) `f` between
[metric spaces](metric-spaces.metric-spaces.md) `X` and `Y` is
{{#concept "uniformly continuous" Disambiguation="function between metric spaces" WDID=Q741865 WD="uniform continuity" Agda=is-uniformly-continuous-map-Metric-Space}}
if there exists a function `m : ℚ⁺ → ℚ⁺` such that for any `x : X`, whenever
`x'` is in an `m ε`-neighborhood of `x`, `f x'` is in an `ε`-neighborhood of
`f x`. The function `m` is called a modulus of uniform continuity of `f`.

## Definitions

### The property of being a uniformly continuous function

```agda
module _
  {l1 l2 l3 l4 : Level} (X : Metric-Space l1 l2) (Y : Metric-Space l3 l4)
  (f : map-type-Metric-Space X Y)
  where

  is-modulus-of-uniform-continuity-prop-Metric-Space :
    (ℚ⁺ → ℚ⁺) → Prop (l1 ⊔ l2 ⊔ l4)
  is-modulus-of-uniform-continuity-prop-Metric-Space =
    is-modulus-of-uniform-continuity-prop-Premetric-Space
      ( premetric-Metric-Space X)
      ( premetric-Metric-Space Y)
      ( f)

  modulus-of-uniform-continuity-map-Metric-Space : UU (l1 ⊔ l2 ⊔ l4)
  modulus-of-uniform-continuity-map-Metric-Space =
    type-subtype is-modulus-of-uniform-continuity-prop-Metric-Space

  is-uniformly-continuous-map-prop-Metric-Space : Prop (l1 ⊔ l2 ⊔ l4)
  is-uniformly-continuous-map-prop-Metric-Space =
    is-uniformly-continuous-map-prop-Premetric-Space
      ( premetric-Metric-Space X)
      ( premetric-Metric-Space Y)
      ( f)

  is-uniformly-continuous-map-Metric-Space : UU (l1 ⊔ l2 ⊔ l4)
  is-uniformly-continuous-map-Metric-Space =
    is-uniformly-continuous-map-Premetric-Space
      ( premetric-Metric-Space X)
      ( premetric-Metric-Space Y)
      ( f)

  is-continuous-at-point-is-uniformly-continuous-map-Metric-Space :
    is-uniformly-continuous-map-Metric-Space → (x : type-Metric-Space X) →
    is-continuous-at-point-Metric-Space X Y f x
  is-continuous-at-point-is-uniformly-continuous-map-Metric-Space =
    is-continuous-at-point-is-uniformly-continuous-map-Premetric-Space
      ( premetric-Metric-Space X)
      ( premetric-Metric-Space Y)
      ( f)
```

### The type of uniformly continuous functions between metric spaces

```agda
module _
  {l1 l2 l3 l4 : Level} (X : Metric-Space l1 l2) (Y : Metric-Space l3 l4)
  where

  uniformly-continuous-map-Metric-Space : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  uniformly-continuous-map-Metric-Space =
    type-subtype (is-uniformly-continuous-map-prop-Metric-Space X Y)
```

## Properties

### The identity function is uniformly continuous

```agda
module _
  {l1 l2 : Level} (X : Metric-Space l1 l2)
  where

  is-uniformly-continuous-map-id-Metric-Space :
    is-uniformly-continuous-map-Metric-Space X X id
  is-uniformly-continuous-map-id-Metric-Space =
    is-uniformly-continuous-map-id-Premetric-Space
      ( premetric-Metric-Space X)
```

### The composition of uniformly continuous functions is uniformly continuous

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  (X : Metric-Space l1 l2) (Y : Metric-Space l3 l4) (Z : Metric-Space l5 l6)
  (f : map-type-Metric-Space Y Z) (g : map-type-Metric-Space X Y)
  where

  is-uniformly-continuous-map-comp-Metric-Space :
    is-uniformly-continuous-map-Metric-Space Y Z f →
    is-uniformly-continuous-map-Metric-Space X Y g →
    is-uniformly-continuous-map-Metric-Space X Z (f ∘ g)
  is-uniformly-continuous-map-comp-Metric-Space =
    is-uniformly-continuous-map-comp-Premetric-Space
      ( premetric-Metric-Space X)
      ( premetric-Metric-Space Y)
      ( premetric-Metric-Space Z)
      ( f)
      ( g)
```
