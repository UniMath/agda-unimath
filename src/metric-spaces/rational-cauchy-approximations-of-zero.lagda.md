# Rational Cauchy approximations of zero

```agda
{-# OPTIONS --lossy-unification #-}

module metric-spaces.rational-cauchy-approximations-of-zero where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.absolute-value-rational-numbers
open import elementary-number-theory.addition-rational-numbers
open import elementary-number-theory.difference-rational-numbers
open import elementary-number-theory.distance-rational-numbers
open import elementary-number-theory.inequality-rational-numbers
open import elementary-number-theory.nonnegative-rational-numbers
open import elementary-number-theory.positive-rational-numbers
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.strict-inequality-rational-numbers

open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.identity-types
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
module _
  (f : cauchy-approximation-ℚ)
  where

  subtype-zero-cauchy-approximation-ℚ : Prop lzero
  subtype-zero-cauchy-approximation-ℚ =
    is-limit-cauchy-approximation-prop-Metric-Space
      metric-space-leq-ℚ
      f
      zero-ℚ

  is-zero-cauchy-approximation-ℚ : UU lzero
  is-zero-cauchy-approximation-ℚ =
    type-Prop subtype-zero-cauchy-approximation-ℚ

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

### Sublinear rational approximations

```agda
module _
  (f : ℚ⁺ → ℚ)
  where

  is-sublinear-approximation-prop-ℚ : Prop lzero
  is-sublinear-approximation-prop-ℚ =
    Π-Prop
      ( ℚ⁺)
      ( λ ε → leq-ℚ-Prop (rational-abs-ℚ (f ε)) (rational-ℚ⁺ ε))

  is-sublinear-approximation-ℚ : UU lzero
  is-sublinear-approximation-ℚ =
    type-Prop is-sublinear-approximation-prop-ℚ

sublinear-approximation-ℚ : UU lzero
sublinear-approximation-ℚ = type-subtype is-sublinear-approximation-prop-ℚ

module _
  (f : sublinear-approximation-ℚ)
  where

  map-sublinear-approximation-ℚ : ℚ⁺ → ℚ
  map-sublinear-approximation-ℚ = pr1 f

  is-sublinear-map-sublinear-approximation-ℚ :
    is-sublinear-approximation-ℚ map-sublinear-approximation-ℚ
  is-sublinear-map-sublinear-approximation-ℚ = pr2 f
```

## Properties

### A rational Cauchy approximation of zero is sublinear

```agda
abstract
  is-sublinear-is-zero-cauchy-approximation-ℚ :
    (f : cauchy-approximation-ℚ) →
    is-zero-cauchy-approximation-ℚ f →
    ( is-sublinear-approximation-ℚ (map-cauchy-approximation-ℚ f))
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

sublinear-zero-cauchy-approximation-ℚ :
  zero-cauchy-approximation-ℚ → sublinear-approximation-ℚ
sublinear-zero-cauchy-approximation-ℚ f =
  ( map-zero-cauchy-approximation-ℚ f) ,
  ( is-sublinear-is-zero-cauchy-approximation-ℚ
    ( approximation-zero-cauchy-approximation-ℚ f)
    ( is-zero-limit-approximation-zero-cauchy-approximation-ℚ f))
```

### Any sublinear map `ℚ⁺ → ℚ` is a Cauchy approximation of zero

```agda
module _
  (f : ℚ⁺ → ℚ)
  (is-sublinear-f : is-sublinear-approximation-ℚ f)
  where

  abstract
    is-cauchy-approximation-is-sublinear-approximation-ℚ :
      is-cauchy-approximation-Metric-Space
        metric-space-leq-ℚ
        f
    is-cauchy-approximation-is-sublinear-approximation-ℚ ε δ =
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
            ( is-sublinear-f ε)
            ( is-sublinear-f δ))
          ( leq-dist-add-abs-ℚ (f ε) (f δ)))

  cauchy-approximation-is-sublinear-approximation-ℚ :
    cauchy-approximation-ℚ
  cauchy-approximation-is-sublinear-approximation-ℚ =
    (f , is-cauchy-approximation-is-sublinear-approximation-ℚ)

  abstract
    is-zero-cauchy-approximation-is-sublinear-approximation-ℚ :
      is-zero-cauchy-approximation-ℚ
        cauchy-approximation-is-sublinear-approximation-ℚ
    is-zero-cauchy-approximation-is-sublinear-approximation-ℚ ε δ =
      neighborhood-leq-leq-dist-ℚ
        ( ε +ℚ⁺ δ)
        ( f ε)
        ( zero-ℚ)
        ( transitive-leq-ℚ
          ( rational-abs-ℚ ((f ε) -ℚ zero-ℚ))
          ( rational-ℚ⁺ ε)
          ( rational-ℚ⁺ (ε +ℚ⁺ δ))
          ( leq-le-ℚ⁺ {ε} {ε +ℚ⁺ δ} (le-left-add-ℚ⁺ ε δ))
          ( inv-tr
            ( λ y → leq-ℚ (rational-ℚ⁰⁺ y) (rational-ℚ⁺ ε))
            ( right-zero-law-dist-ℚ (f ε))
            ( is-sublinear-f ε)))

zero-cauchy-approximation-sublinear-approximation-ℚ :
  sublinear-approximation-ℚ → zero-cauchy-approximation-ℚ
zero-cauchy-approximation-sublinear-approximation-ℚ f =
  ( cauchy-approximation-is-sublinear-approximation-ℚ
    ( map-sublinear-approximation-ℚ f)
    ( is-sublinear-map-sublinear-approximation-ℚ f)) ,
  ( is-zero-cauchy-approximation-is-sublinear-approximation-ℚ
    ( map-sublinear-approximation-ℚ f)
    ( is-sublinear-map-sublinear-approximation-ℚ f))
```

### A rational Cauchy approximation `f` converges to some `x : ℚ` if and only if the map `ε ↦ dist-ℚ (f ε) x` is sublinear, i.e. a Cauchy approximation of zero

```agda
module _
  (f : cauchy-approximation-ℚ) (x : ℚ)
  where

  map-dist-value-cauchy-approximation-ℚ : ℚ⁺ → ℚ
  map-dist-value-cauchy-approximation-ℚ ε =
    rational-dist-ℚ (map-cauchy-approximation-ℚ f ε) x

  abstract
    is-sublinear-map-dist-is-limit-cauchy-approximation-ℚ :
      is-limit-cauchy-approximation-Metric-Space
        ( metric-space-leq-ℚ)
        ( f)
        ( x) →
      is-sublinear-approximation-ℚ map-dist-value-cauchy-approximation-ℚ
    is-sublinear-map-dist-is-limit-cauchy-approximation-ℚ H ε =
      inv-tr
        ( λ y → leq-ℚ (rational-ℚ⁰⁺ y) (rational-ℚ⁺ ε))
        ( abs-rational-ℚ⁰⁺ (dist-ℚ (map-cauchy-approximation-ℚ f ε) x))
        ( leq-dist-neighborhood-leq-ℚ
          ( ε)
          ( map-cauchy-approximation-ℚ f ε)
          ( x)
          ( is-saturated-metric-space-leq-ℚ
            ( ε)
            ( map-cauchy-approximation-ℚ f ε)
            ( x)
            ( H ε)))

    is-limit-is-sublinear-map-dist-cauchy-approximation-ℚ :
      is-sublinear-approximation-ℚ map-dist-value-cauchy-approximation-ℚ →
      is-limit-cauchy-approximation-Metric-Space
        ( metric-space-leq-ℚ)
        ( f)
        ( x)
    is-limit-is-sublinear-map-dist-cauchy-approximation-ℚ H ε δ =
      neighborhood-leq-leq-dist-ℚ
        ( ε +ℚ⁺ δ)
        ( map-cauchy-approximation-ℚ f ε)
        ( x)
        ( transitive-leq-ℚ
          ( rational-dist-ℚ (map-cauchy-approximation-ℚ f ε) x)
          ( rational-ℚ⁺ ε)
          ( rational-ℚ⁺ (ε +ℚ⁺ δ))
          ( leq-le-ℚ⁺ {ε} {ε +ℚ⁺ δ} (le-left-add-ℚ⁺ ε δ))
          ( transitive-leq-ℚ
            ( map-dist-value-cauchy-approximation-ℚ ε)
            ( rational-abs-ℚ (map-dist-value-cauchy-approximation-ℚ ε))
            ( rational-ℚ⁺ ε)
            ( H ε)
            ( leq-abs-ℚ (map-dist-value-cauchy-approximation-ℚ ε))))

    is-cauchy-approximation-dist-is-limit-cauchy-approximation-ℚ :
      is-limit-cauchy-approximation-Metric-Space
        ( metric-space-leq-ℚ)
        ( f)
        ( x) →
      is-cauchy-approximation-Metric-Space
        metric-space-leq-ℚ
        map-dist-value-cauchy-approximation-ℚ
    is-cauchy-approximation-dist-is-limit-cauchy-approximation-ℚ H =
      is-cauchy-approximation-is-sublinear-approximation-ℚ
        ( map-dist-value-cauchy-approximation-ℚ)
        ( is-sublinear-map-dist-is-limit-cauchy-approximation-ℚ H)

    cauchy-approximation-dist-is-limit-cauchy-approximation-ℚ :
      is-limit-cauchy-approximation-Metric-Space
        ( metric-space-leq-ℚ)
        ( f)
        ( x) →
      cauchy-approximation-ℚ
    cauchy-approximation-dist-is-limit-cauchy-approximation-ℚ H =
      cauchy-approximation-is-sublinear-approximation-ℚ
        ( map-dist-value-cauchy-approximation-ℚ)
        ( is-sublinear-map-dist-is-limit-cauchy-approximation-ℚ H)

    is-zero-approximation-dist-is-limit-cauchy-approximation-ℚ :
      ( H : is-limit-cauchy-approximation-Metric-Space
        ( metric-space-leq-ℚ)
        ( f)
        ( x)) →
      is-zero-cauchy-approximation-ℚ
        ( cauchy-approximation-dist-is-limit-cauchy-approximation-ℚ H)
    is-zero-approximation-dist-is-limit-cauchy-approximation-ℚ H =
      is-zero-cauchy-approximation-is-sublinear-approximation-ℚ
        ( map-dist-value-cauchy-approximation-ℚ)
        ( is-sublinear-map-dist-is-limit-cauchy-approximation-ℚ H)

    is-limit-is-zero-approximation-dist-cauchy-approximation-ℚ :
      ( H : is-cauchy-approximation-Metric-Space
        ( metric-space-leq-ℚ)
        ( map-dist-value-cauchy-approximation-ℚ)) →
      ( K : is-zero-cauchy-approximation-ℚ
        ( map-dist-value-cauchy-approximation-ℚ , H)) →
      is-limit-cauchy-approximation-Metric-Space
        ( metric-space-leq-ℚ)
        ( f)
        ( x)
    is-limit-is-zero-approximation-dist-cauchy-approximation-ℚ H K =
      is-limit-is-sublinear-map-dist-cauchy-approximation-ℚ
        ( is-sublinear-is-zero-cauchy-approximation-ℚ
          ( map-dist-value-cauchy-approximation-ℚ , H)
          ( K))
```
