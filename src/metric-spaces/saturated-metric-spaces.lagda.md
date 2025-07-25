# Saturated metric spaces

```agda
module metric-spaces.saturated-metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.positive-rational-numbers

open import foundation.binary-relations
open import foundation.dependent-pair-types
open import foundation.equality-dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.propositions
open import foundation.sets
open import foundation.subtypes
open import foundation.universe-levels

open import metric-spaces.closed-premetric-structures
open import metric-spaces.equality-of-metric-spaces
open import metric-spaces.functions-metric-spaces
open import metric-spaces.metric-spaces
open import metric-spaces.metric-structures
open import metric-spaces.premetric-spaces
open import metric-spaces.premetric-structures
open import metric-spaces.short-functions-metric-spaces
```

</details>

## Idea

A [metric space](metric-spaces.metric-spaces.md) is
{{#concept "saturated" Disambiguation="metric space" Agda=is-saturated-Metric-Space}}
if its [premetric](metric-spaces.premetric-structures.md) is
[closed](metric-spaces.closed-premetric-structures.md).

## Definitions

### The property of being a saturated metric space

```agda
module _
  {l1 l2 : Level} (M : Metric-Space l1 l2)
  where

  is-saturated-prop-Metric-Space : Prop (l1 ⊔ l2)
  is-saturated-prop-Metric-Space =
    is-closed-prop-Premetric (structure-Metric-Space M)

  is-saturated-Metric-Space : UU (l1 ⊔ l2)
  is-saturated-Metric-Space = type-Prop is-saturated-prop-Metric-Space

  is-prop-is-saturated-Metric-Space : is-prop is-saturated-Metric-Space
  is-prop-is-saturated-Metric-Space =
    is-prop-type-Prop is-saturated-prop-Metric-Space
```

### Saturation of a metric space

```agda
module _
  {l1 l2 : Level} (M : Metric-Space l1 l2)
  where

  saturate-Metric-Space : Metric-Space l1 l2
  pr1 saturate-Metric-Space =
    type-Metric-Space M , closure-Premetric (structure-Metric-Space M)
  pr2 saturate-Metric-Space =
    preserves-is-metric-closure-Premetric
      ( structure-Metric-Space M)
      ( is-metric-structure-Metric-Space M)
```

## Properties

### The saturation of a metric space is saturated

```agda
module _
  {l1 l2 : Level} (M : Metric-Space l1 l2)
  where

  is-saturated-saturate-Metric-Space :
    is-saturated-Metric-Space (saturate-Metric-Space M)
  is-saturated-saturate-Metric-Space =
    is-closed-closure-Premetric (structure-Metric-Space M)
```

### The saturation of a saturated metric space is itself

```agda
module _
  {l1 l2 : Level} (M : Metric-Space l1 l2)
  (H : is-saturated-Metric-Space M)
  where

  eq-saturate-is-saturated-Metric-Space :
    saturate-Metric-Space M ＝ M
  eq-saturate-is-saturated-Metric-Space =
    eq-type-subtype
      ( is-metric-prop-Premetric-Space)
      ( eq-pair-eq-fiber
        ( eq-closure-closed-monotonic-Premetric
          ( structure-Metric-Space M)
          ( is-monotonic-structure-Metric-Space M)
          ( H)))
```

### Saturation of metric spaces is idempotent

```agda
module _
  {l1 l2 : Level} (M : Metric-Space l1 l2)
  where

  is-idempotent-saturate-Metric-Space :
    saturate-Metric-Space (saturate-Metric-Space M) ＝
    saturate-Metric-Space M
  is-idempotent-saturate-Metric-Space =
    eq-saturate-is-saturated-Metric-Space
      ( saturate-Metric-Space M)
      ( is-saturated-saturate-Metric-Space M)
```

### The identity map between a metric space and its saturation is short

```agda
module _
  {l1 l2 : Level} (M : Metric-Space l1 l2)
  where

  is-short-id-saturate-Metric-Space :
    is-short-function-Metric-Space
      ( M)
      ( saturate-Metric-Space M)
      ( id)
  is-short-id-saturate-Metric-Space =
    leq-closure-monotonic-Premetric
      ( structure-Metric-Space M)
      ( is-monotonic-structure-Metric-Space M)

  short-id-saturate-Metric-Space :
    short-function-Metric-Space M (saturate-Metric-Space M)
  short-id-saturate-Metric-Space =
    id , is-short-id-saturate-Metric-Space
```

### Saturation of metric spaces preserves short maps into saturated metric spaces

```agda
module _
  {l1 l2 l1' l2' : Level} (M : Metric-Space l1 l2) (M' : Metric-Space l1' l2')
  (S' : is-saturated-Metric-Space M')
  (f : map-type-Metric-Space M M')
  where

  is-short-saturate-short-function-saturated-Metric-Space :
    is-short-function-Metric-Space M M' f →
    is-short-function-Metric-Space (saturate-Metric-Space M) M' f
  is-short-saturate-short-function-saturated-Metric-Space H d x y I =
    S' d (f x) (f y) (λ δ → H (d +ℚ⁺ δ) x y (I δ))

  is-short-is-short-saturate-function-saturated-Metric-Space :
    is-short-function-Metric-Space (saturate-Metric-Space M) M' f →
    is-short-function-Metric-Space M M' f
  is-short-is-short-saturate-function-saturated-Metric-Space H =
    is-short-map-short-function-Metric-Space
      ( M)
      ( M')
      ( comp-short-function-Metric-Space
        ( M)
        ( saturate-Metric-Space M)
        ( M')
        ( f , H)
        ( short-id-saturate-Metric-Space M))

  equiv-saturate-is-short-function-saturated-Metric-Space :
    (is-short-function-Metric-Space M M' f) ≃
    (is-short-function-Metric-Space (saturate-Metric-Space M) M' f)
  equiv-saturate-is-short-function-saturated-Metric-Space =
    equiv-iff
      ( is-short-function-prop-Metric-Space M M' f)
      ( is-short-function-prop-Metric-Space (saturate-Metric-Space M) M' f)
      ( is-short-saturate-short-function-saturated-Metric-Space)
      ( is-short-is-short-saturate-function-saturated-Metric-Space)
```

```agda
module _
  {l1 l2 l1' l2' : Level} (M : Metric-Space l1 l2) (M' : Metric-Space l1' l2')
  (S' : is-saturated-Metric-Space M')
  where

  equiv-short-function-saturated-Metric-Space :
    short-function-Metric-Space M M' ≃
    short-function-Metric-Space (saturate-Metric-Space M) M'
  equiv-short-function-saturated-Metric-Space =
    equiv-tot (equiv-saturate-is-short-function-saturated-Metric-Space M M' S')
```
