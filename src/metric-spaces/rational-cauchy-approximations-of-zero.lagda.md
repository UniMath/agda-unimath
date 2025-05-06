# Rational Cauchy approximations of zero

```agda
{-# OPTIONS --lossy-unification #-}

module metric-spaces.rational-cauchy-approximations-of-zero where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.absolute-value-rational-numbers
open import elementary-number-theory.addition-rational-numbers
open import elementary-number-theory.distance-rational-numbers
open import elementary-number-theory.inequality-rational-numbers
open import elementary-number-theory.nonnegative-rational-numbers
open import elementary-number-theory.positive-rational-numbers
open import elementary-number-theory.rational-numbers

open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.propositions
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import metric-spaces.cauchy-approximations-metric-spaces
open import metric-spaces.convergent-cauchy-approximations-metric-spaces
open import metric-spaces.limits-of-cauchy-approximations-premetric-spaces
open import metric-spaces.metric-space-of-rational-numbers
open import metric-spaces.metric-spaces
open import metric-spaces.rational-cauchy-approximations
```

</details>

## Idea

{{#concept "Rational Cauchy approximations of zero" Agda=zero-cauchy-approximation-ℚ}}
are
[Cauchy approximations](metric-spaces.cauchy-approximations-metric-spaces.md) in
the
[metric space of rational numbers](metric-spaces.metric-space-of-rational-numbers.md)
that [converge](metric-spaces.convergent-cauchy-approximations-metric-spaces.md)
to [zero-ℚ](elementary-number-theory.rational-numbers.md).

## Definitions

### The type of rational Cauchy approximations of zero

```agda
subtype-zero-cauchy-approximation-ℚ : subtype lzero cauchy-approximation-ℚ
subtype-zero-cauchy-approximation-ℚ f =
  is-limit-cauchy-approximation-prop-Metric-Space
    metric-space-leq-ℚ
    f
    zero-ℚ

is-zero-cauchy-approximation-ℚ : cauchy-approximation-ℚ → UU lzero
is-zero-cauchy-approximation-ℚ f =
  type-Prop (subtype-zero-cauchy-approximation-ℚ f)

zero-cauchy-approximation-ℚ : UU lzero
zero-cauchy-approximation-ℚ = type-subtype subtype-zero-cauchy-approximation-ℚ

module _
  (z : zero-cauchy-approximation-ℚ)
  where

  approximation-zero-cauchy-approximation-ℚ :
    cauchy-approximation-ℚ
  approximation-zero-cauchy-approximation-ℚ = pr1 z

  is-zero-limit-approximation-zero-cauchy-approximation-ℚ :
    is-limit-cauchy-approximation-Metric-Space
      metric-space-leq-ℚ
      approximation-zero-cauchy-approximation-ℚ
      zero-ℚ
  is-zero-limit-approximation-zero-cauchy-approximation-ℚ = pr2 z

  map-zero-cauchy-approximation-ℚ : ℚ⁺ → ℚ
  map-zero-cauchy-approximation-ℚ =
    map-cauchy-approximation-ℚ approximation-zero-cauchy-approximation-ℚ

  is-cauchy-map-zero-cauchy-approximation-ℚ :
    is-cauchy-approximation-Metric-Space
      metric-space-leq-ℚ
      map-zero-cauchy-approximation-ℚ
  is-cauchy-map-zero-cauchy-approximation-ℚ =
    is-cauchy-map-cauchy-approximation-ℚ
      approximation-zero-cauchy-approximation-ℚ
```

## Properties

### A rational Cauchy approximation of zero is sub-linear

```agda
abstract
  is-sublinear-is-zero-cauchy-approximation-ℚ :
    (f : cauchy-approximation-ℚ) →
    is-zero-cauchy-approximation-ℚ f →
    (ε : ℚ⁺) →
    leq-ℚ (rational-abs-ℚ (map-cauchy-approximation-ℚ f ε)) (rational-ℚ⁺ ε)
  is-sublinear-is-zero-cauchy-approximation-ℚ f H ε =
    tr
      ( λ y → leq-ℚ y (rational-ℚ⁺ ε))
      ( ap
        ( rational-ℚ⁰⁺)
        ( right-zero-law-dist-ℚ (map-cauchy-approximation-ℚ f ε)))
      ( leq-dist-neighborhood-leq-ℚ
        ( ε)
        ( map-cauchy-approximation-ℚ f ε)
        ( zero-ℚ)
        ( is-saturated-metric-space-leq-ℚ
          ( ε)
          ( map-cauchy-approximation-ℚ f ε)
          ( zero-ℚ)
          ( H ε)))
```

### Any sublinear map `ℚ⁺ → ℚ` is a Cauchy approximation of zero

```agda
module _
  (f : ℚ⁺ → ℚ)
  (sublinear-f : (x : ℚ⁺) → leq-ℚ (rational-abs-ℚ (f x)) (rational-ℚ⁺ x))
  where

  abstract
    is-cauchy-approximation-is-sublinear-map-ℚ :
      is-cauchy-approximation-Metric-Space
        metric-space-leq-ℚ
        f
    is-cauchy-approximation-is-sublinear-map-ℚ ε δ =
      neighborhood-leq-leq-dist-ℚ
        ( ε +ℚ⁺ δ)
        ( f ε)
        ( f δ)
        ( transitive-leq-ℚ
          ( rational-dist-ℚ (f ε) (f δ))
          ( (rational-abs-ℚ (f ε)) +ℚ (rational-abs-ℚ (f δ)))
          ( rational-ℚ⁺ (ε +ℚ⁺ δ))
          ( preserves-leq-add-ℚ
            { rational-abs-ℚ (f ε)}
            { rational-ℚ⁺ ε}
            { rational-abs-ℚ (f δ)}
            { rational-ℚ⁺ δ}
            ( sublinear-f ε)
            ( sublinear-f δ))
          ( leq-dist-add-abs-ℚ (f ε) (f δ)))
```
