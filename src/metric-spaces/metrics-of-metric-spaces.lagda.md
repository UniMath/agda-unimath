# Metrics of metric spaces

```agda
module metric-spaces.metrics-of-metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.positive-rational-numbers

open import foundation.dependent-pair-types
open import foundation.logical-equivalences
open import foundation.propositions
open import foundation.sets
open import foundation.universe-levels

open import metric-spaces.metric-spaces
open import metric-spaces.metrics

open import real-numbers.nonnegative-real-numbers
```

</details>

## Idea

A function `ρ` from two elements of a
[metric space](metric-spaces.metric-spaces.md) `M` to the
[nonnegative real numbers](real-numbers.nonnegative-real-numbers.md) is a
{{#concept "metric" disambiguation="of a metric space" Agda=is-metric-Metric-Space}}
of `M` if for all
[positive rational numbers](elementary-number-theory.positive-rational-numbers.md)
`d` and all `x y : M`, `x` and `y` are in a `d`-neighborhood of each other in
`M` [if and only if](foundation.logical-equivalences.md) `ρ x y ≤ real-ℚ⁺ d`.

It follows that `ρ` is a [metric](metric-spaces.metrics.md) on the
[set](foundation.sets.md) of elements of `M`, and and that `M` is
[isometrically equivalent](metric-spaces.equality-of-metric-spaces.md)
to the metric space induced by `ρ`.

## Definition

```agda
module _
  {l1 l2 l3 : Level} (M : Metric-Space l1 l2)
  (ρ : distance-function l3 (set-Metric-Space M))
  where

  is-metric-prop-Metric-Space : Prop (l1 ⊔ l2 ⊔ l3)
  is-metric-prop-Metric-Space =
    Π-Prop ℚ⁺
      ( λ d →
        Π-Prop
          ( type-Metric-Space M)
          ( λ x →
            Π-Prop
              ( type-Metric-Space M)
              ( λ y →
                neighborhood-prop-Metric-Space M d x y ⇔
                leq-prop-ℝ⁰⁺ (ρ x y) (nonnegative-real-ℚ⁺ d))))

  is-metric-of-Metric-Space : UU (l1 ⊔ l2 ⊔ l3)
  is-metric-of-Metric-Space = type-Prop is-metric-prop-Metric-Space
```

## Properties

### A metric is a metric of the metric space it induces

```agda
module _
  {l1 l2 : Level} (X : Set l1) (ρ : Metric l2 X)
  where

  is-metric-metric-space-Metric :
    is-metric-of-Metric-Space
      ( metric-space-Metric X ρ)
      ( dist-Metric X ρ)
  is-metric-metric-space-Metric _ _ _ = id-iff
```

### If `ρ` is a metric for a metric space, it is a metric

```agda
module _
  {l1 l2 l3 : Level} (M : Metric-Space l1 l2)
  (ρ : distance-function l3 (set-Metric-Space M))
  (is-metric-M-ρ : is-metric-of-Metric-Space M ρ)
  where

  abstract
    is-reflexive-is-metric-of-Metric-Space :
      is-reflexive-distance-function (set-Metric-Space M) ρ
    is-reflexive-is-metric-of-Metric-Space x =
      sim-zero-le-positive-rational-ℝ⁰⁺
        ( ρ x x)
        ( λ ε →
          forward-implication
            ( is-metric-M-ρ ε x x)
            ( refl-neighborhood-Metric-Space M ε x))

    is-symmetric-is-metric-of-Metric-Space :
      is-symmetric-distance-function (set-Metric-Space M) ρ
    is-symmetric-is-metric-of-Metric-Space x y =
      eq-sim-ℝ⁰⁺ (ρ x y) (ρ y x)
        ( sim-leq-same-positive-rational-ℝ⁰⁺ (ρ x y) (ρ y x)
          ( λ d →
            is-metric-M-ρ d y x ∘iff
            ( symmetric-neighborhood-Metric-Space M d x y ,
              symmetric-neighborhood-Metric-Space M d y x) ∘iff
            inv-iff (is-metric-M-ρ d x y)))

    is-triangular-is-metric-of-Metric-Space :
      is-triangular-distance-function (set-Metric-Space M) ρ
    is-triangular-is-metric-of-Metric-Space x y z =
      leq-leq-positive-rational-ℝ⁰⁺ (ρ x z) (ρ x y +ℝ⁰⁺ ρ y z)
        ( λ d ρxy+ρyz≤d →
          forward-implication
            ( is-metric-M-ρ d x z)
            {!   !})
```
