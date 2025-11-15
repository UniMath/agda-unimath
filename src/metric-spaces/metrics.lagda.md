# Metrics

```agda
{-# OPTIONS --lossy-unification #-}

module metric-spaces.metrics where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-positive-rational-numbers
open import elementary-number-theory.nonnegative-rational-numbers
open import elementary-number-theory.positive-rational-numbers

open import foundation.conjunction
open import foundation.dependent-pair-types
open import foundation.disjunction
open import foundation.functoriality-disjunction
open import foundation.identity-types
open import foundation.negation
open import foundation.propositions
open import foundation.sets
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import logic.functoriality-existential-quantification

open import metric-spaces.elements-at-bounded-distance-metric-spaces
open import metric-spaces.extensionality-pseudometric-spaces
open import metric-spaces.located-metric-spaces
open import metric-spaces.metric-spaces
open import metric-spaces.pseudometric-spaces
open import metric-spaces.rational-neighborhood-relations
open import metric-spaces.reflexive-rational-neighborhood-relations
open import metric-spaces.saturated-rational-neighborhood-relations
open import metric-spaces.symmetric-rational-neighborhood-relations
open import metric-spaces.triangular-rational-neighborhood-relations

open import real-numbers.addition-nonnegative-real-numbers
open import real-numbers.dedekind-real-numbers
open import real-numbers.inequality-nonnegative-real-numbers
open import real-numbers.nonnegative-real-numbers
open import real-numbers.rational-real-numbers
open import real-numbers.saturation-inequality-nonnegative-real-numbers
open import real-numbers.similarity-nonnegative-real-numbers
open import real-numbers.strict-inequality-nonnegative-real-numbers
open import real-numbers.strict-inequality-real-numbers
```

</details>

## Idea

A {{#concept "metric" WDID=Q865746 WD="metric function" Agda=Metric}} on a
[set](foundation.sets.md) `X` is a function `d` from two elements of `X` to the
[nonnegative real numbers](real-numbers.nonnegative-real-numbers.md) with the
following properties:

- **Reflexivity.** `d x x ＝ 0` for all `x : X`.
- **Symmetry.** `d x y = d y x` for all `x y : X`.
- **Triangularity.** `d x z ≤ d x y + d y z` for all `x y z : X`.
- **Extensionality.** `d x y = 0` implies `x ＝ y` for all `x y : X`.

A metric induces a unique [located](metric-spaces.located-metric-spaces.md)
[metric space](metric-spaces.metric-spaces.md) in which every pair of elements
is at
[bounded distance](metric-spaces.elements-at-bounded-distance-metric-spaces.md).

## Definition

```agda
distance-function : {l1 : Level} → (l2 : Level) → Set l1 → UU (l1 ⊔ lsuc l2)
distance-function l2 X = type-Set X → type-Set X → nonnegative-ℝ l2

module _
  {l1 l2 : Level} (X : Set l1) (d : distance-function l2 X)
  where

  is-reflexive-prop-distance-function : Prop (l1 ⊔ l2)
  is-reflexive-prop-distance-function =
    Π-Prop (type-Set X) (λ x → sim-zero-prop-ℝ⁰⁺ (d x x))

  is-reflexive-distance-function : UU (l1 ⊔ l2)
  is-reflexive-distance-function = type-Prop is-reflexive-prop-distance-function

  is-symmetric-prop-distance-function : Prop (l1 ⊔ lsuc l2)
  is-symmetric-prop-distance-function =
    Π-Prop
      ( type-Set X)
      ( λ x →
        Π-Prop
          ( type-Set X)
          ( λ y → Id-Prop (ℝ⁰⁺-Set l2) (d x y) (d y x)))

  is-symmetric-distance-function : UU (l1 ⊔ lsuc l2)
  is-symmetric-distance-function = type-Prop is-symmetric-prop-distance-function

  is-triangular-prop-distance-function : Prop (l1 ⊔ l2)
  is-triangular-prop-distance-function =
    Π-Prop
      ( type-Set X)
      ( λ x →
        Π-Prop
          ( type-Set X)
          ( λ y →
            Π-Prop
              ( type-Set X)
              ( λ z → leq-prop-ℝ⁰⁺ (d x z) (d x y +ℝ⁰⁺ d y z))))

  is-triangular-distance-function : UU (l1 ⊔ l2)
  is-triangular-distance-function =
    type-Prop is-triangular-prop-distance-function

  is-extensional-prop-distance-function : Prop (l1 ⊔ l2)
  is-extensional-prop-distance-function =
    Π-Prop
      ( type-Set X)
      ( λ x →
        Π-Prop
          ( type-Set X)
          ( λ y →
            hom-Prop (sim-zero-prop-ℝ⁰⁺ (d x y)) (Id-Prop X x y)))

  is-extensional-distance-function : UU (l1 ⊔ l2)
  is-extensional-distance-function =
    type-Prop is-extensional-prop-distance-function

  is-metric-prop-distance-function : Prop (l1 ⊔ lsuc l2)
  is-metric-prop-distance-function =
    is-reflexive-prop-distance-function ∧
    is-symmetric-prop-distance-function ∧
    is-triangular-prop-distance-function ∧
    is-extensional-prop-distance-function

  is-metric-distance-function : UU (l1 ⊔ lsuc l2)
  is-metric-distance-function = type-Prop is-metric-prop-distance-function

Metric : {l1 : Level} (l2 : Level) (X : Set l1) → UU (l1 ⊔ lsuc l2)
Metric l2 X = type-subtype (is-metric-prop-distance-function {l2 = l2} X)

module _
  {l1 l2 : Level} (X : Set l1) (μ : Metric l2 X)
  where

  dist-Metric : distance-function l2 X
  dist-Metric = pr1 μ

  is-reflexive-dist-Metric : (x : type-Set X) → sim-zero-ℝ⁰⁺ (dist-Metric x x)
  is-reflexive-dist-Metric = pr1 (pr2 μ)

  is-symmetric-dist-Metric :
    (x y : type-Set X) → dist-Metric x y ＝ dist-Metric y x
  is-symmetric-dist-Metric = pr1 (pr2 (pr2 μ))

  is-triangular-dist-Metric :
    (x y z : type-Set X) →
    leq-ℝ⁰⁺ (dist-Metric x z) (dist-Metric x y +ℝ⁰⁺ dist-Metric y z)
  is-triangular-dist-Metric = pr1 (pr2 (pr2 (pr2 μ)))

  is-extensional-dist-Metric :
    (x y : type-Set X) → sim-zero-ℝ⁰⁺ (dist-Metric x y) → x ＝ y
  is-extensional-dist-Metric = pr2 (pr2 (pr2 (pr2 μ)))
```

## Properties

### The rational neighborhood relation induced by a metric

```agda
module _
  {l1 l2 : Level} (X : Set l1) (μ : Metric l2 X)
  where

  neighborhood-prop-Metric :
    Rational-Neighborhood-Relation l2 (type-Set X)
  neighborhood-prop-Metric ε x y =
    leq-prop-ℝ⁰⁺ (dist-Metric X μ x y) (nonnegative-real-ℚ⁺ ε)
```

### The rational neighborhood relation induced by a metric is reflexive

```agda
module _
  {l1 l2 : Level} (X : Set l1) (μ : Metric l2 X)
  where

  abstract
    is-reflexive-neighborhood-prop-Metric :
      is-reflexive-Rational-Neighborhood-Relation (neighborhood-prop-Metric X μ)
    is-reflexive-neighborhood-prop-Metric ε x =
      preserves-leq-left-sim-ℝ⁰⁺
        ( nonnegative-real-ℚ⁺ ε)
        ( zero-ℝ⁰⁺)
        ( dist-Metric X μ x x)
        ( is-reflexive-dist-Metric X μ x)
        ( leq-zero-ℝ⁰⁺ (nonnegative-real-ℚ⁺ ε))
```

### The rational neighborhood relation induced by a metric is symmetric

```agda
module _
  {l1 l2 : Level} (X : Set l1) (μ : Metric l2 X)
  where

  abstract
    is-symmetric-neighborhood-prop-Metric :
      is-symmetric-Rational-Neighborhood-Relation (neighborhood-prop-Metric X μ)
    is-symmetric-neighborhood-prop-Metric ε x y =
      tr
        ( λ d → leq-ℝ⁰⁺ d (nonnegative-real-ℚ⁺ ε))
        ( is-symmetric-dist-Metric X μ x y)
```

### The rational neighborhood relation induced by a metric is triangular

```agda
module _
  {l1 l2 : Level} (X : Set l1) (μ : Metric l2 X)
  where

  abstract
    is-triangular-neighborhood-prop-Metric :
      is-triangular-Rational-Neighborhood-Relation
        ( neighborhood-prop-Metric X μ)
    is-triangular-neighborhood-prop-Metric x y z εxy εyz dyz≤εyz dxy≤εxy =
      transitive-leq-ℝ⁰⁺
        ( dist-Metric X μ x z)
        ( dist-Metric X μ x y +ℝ⁰⁺ dist-Metric X μ y z)
        ( nonnegative-real-ℚ⁺ (εxy +ℚ⁺ εyz))
        ( tr
          ( leq-ℝ⁰⁺ (dist-Metric X μ x y +ℝ⁰⁺ dist-Metric X μ y z))
          ( add-nonnegative-real-ℚ⁺ εxy εyz)
          ( preserves-leq-add-ℝ⁰⁺
            ( dist-Metric X μ x y)
            ( nonnegative-real-ℚ⁺ εxy)
            ( dist-Metric X μ y z)
            ( nonnegative-real-ℚ⁺ εyz)
            ( dxy≤εxy)
            ( dyz≤εyz)))
        ( is-triangular-dist-Metric X μ x y z)
```

### The rational neighborhood relation induced by a metric is saturated

```agda
module _
  {l1 l2 : Level} (X : Set l1) (μ : Metric l2 X)
  where

  abstract
    is-saturated-neighborhood-prop-Metric :
      is-saturated-Rational-Neighborhood-Relation
        ( neighborhood-prop-Metric X μ)
    is-saturated-neighborhood-prop-Metric ε x y H =
      saturated-leq-ℝ⁰⁺
        ( dist-Metric X μ x y)
        ( nonnegative-real-ℚ⁺ ε)
        ( λ δ →
          inv-tr
            ( leq-ℝ⁰⁺ (dist-Metric X μ x y))
            ( add-nonnegative-real-ℚ⁺ ε δ)
            ( H δ))
```

### The pseudometric space induced by a metric

```agda
module _
  {l1 l2 : Level} (X : Set l1) (μ : Metric l2 X)
  where

  pseudometric-structure-Metric : Pseudometric-Structure l2 (type-Set X)
  pseudometric-structure-Metric =
    ( neighborhood-prop-Metric X μ ,
      is-reflexive-neighborhood-prop-Metric X μ ,
      is-symmetric-neighborhood-prop-Metric X μ ,
      is-triangular-neighborhood-prop-Metric X μ ,
      is-saturated-neighborhood-prop-Metric X μ)

  pseudometric-space-Metric : Pseudometric-Space l1 l2
  pseudometric-space-Metric =
    ( type-Set X , pseudometric-structure-Metric)
```

### The pseudometric space induced by a metric is tight

```agda
module _
  {l1 l2 : Level} (X : Set l1) (μ : Metric l2 X)
  where

  abstract
    is-tight-pseudometric-space-Metric :
      is-tight-Pseudometric-Space (pseudometric-space-Metric X μ)
    is-tight-pseudometric-space-Metric x y H =
      is-extensional-dist-Metric X μ x y
        ( sim-zero-le-positive-rational-ℝ⁰⁺ (dist-Metric X μ x y) H)
```

### The pseudometric space induced by a metric is extensional

```agda
module _
  {l1 l2 : Level} (X : Set l1) (μ : Metric l2 X)
  where

  abstract
    is-extensional-pseudometric-space-Metric :
      is-extensional-Pseudometric-Space (pseudometric-space-Metric X μ)
    is-extensional-pseudometric-space-Metric =
      is-extensional-is-tight-Pseudometric-Space
        ( pseudometric-space-Metric X μ)
        ( is-tight-pseudometric-space-Metric X μ)
```

### The metric space induced by a metric

```agda
module _
  {l1 l2 : Level} (X : Set l1) (μ : Metric l2 X)
  where

  metric-space-Metric : Metric-Space l1 l2
  metric-space-Metric =
    ( pseudometric-space-Metric X μ ,
      is-extensional-pseudometric-space-Metric X μ)
```

### The metric space induced by a metric is located

```agda
module _
  {l1 l2 : Level} (X : Set l1) (μ : Metric l2 X)
  where

  abstract
    is-located-metric-space-Metric :
      is-located-Metric-Space (metric-space-Metric X μ)
    is-located-metric-space-Metric x y δ ε δ<ε =
      map-disjunction
        ( not-leq-le-ℝ
          ( real-ℚ⁺ δ)
          ( real-ℝ⁰⁺ (dist-Metric X μ x y)))
        ( leq-le-ℝ)
        ( is-located-le-ℝ
          ( real-ℝ⁰⁺ (dist-Metric X μ x y))
          ( rational-ℚ⁺ δ)
          ( rational-ℚ⁺ ε)
          ( δ<ε))

  located-metric-space-Metric : Located-Metric-Space l1 l2
  located-metric-space-Metric =
    ( metric-space-Metric X μ , is-located-metric-space-Metric)
```

### Every element in a located metric space is at bounded distance

```agda
module _
  {l1 l2 : Level} (X : Set l1) (μ : Metric l2 X)
  where

  abstract
    bounded-dist-metric-space-Metric :
      (x y : type-Set X) →
      bounded-dist-Metric-Space (metric-space-Metric X μ) x y
    bounded-dist-metric-space-Metric x y =
      map-tot-exists
        ( λ ε → leq-le-ℝ)
        ( le-some-positive-rational-ℝ⁰⁺ (dist-Metric X μ x y))
```
