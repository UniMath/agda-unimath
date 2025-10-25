# Rational approximations of zero

```agda
{-# OPTIONS --lossy-unification #-}

module metric-spaces.rational-approximations-of-zero where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.absolute-value-rational-numbers
open import elementary-number-theory.addition-positive-rational-numbers
open import elementary-number-theory.addition-rational-numbers
open import elementary-number-theory.difference-rational-numbers
open import elementary-number-theory.distance-rational-numbers
open import elementary-number-theory.inequality-rational-numbers
open import elementary-number-theory.nonnegative-rational-numbers
open import elementary-number-theory.positive-rational-numbers
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.strict-inequality-positive-rational-numbers

open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.functoriality-dependent-pair-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.retractions
open import foundation.sections
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import metric-spaces.cauchy-approximations-metric-spaces
open import metric-spaces.convergent-cauchy-approximations-metric-spaces
open import metric-spaces.limits-of-cauchy-approximations-metric-spaces
open import metric-spaces.metric-space-of-rational-numbers
open import metric-spaces.metric-spaces
open import metric-spaces.rational-cauchy-approximations
```

</details>

## Idea

A map from the
[positive rational numbers](elementary-number-theory.positive-rational-numbers.md)
to the [rationals](elementary-number-theory.rational-numbers.md) `f : ℚ⁺ → ℚ` is
a {{#concept "rational approximation of zero"  Agda=approximation-of-zero-ℚ}} if
`|f ε| ≤ ε` for all `ε : ℚ⁺`. The type of rational approximations of zero is
[equivalent](foundation.equivalences.md) to the type of
[rational Cauchy approximations](metric-spaces.rational-cauchy-approximations.md)
[converging](metric-spaces.convergent-cauchy-approximations-metric-spaces.md) to
zero.

## Definitions

### Rational approximations of zero

```agda
module _
  (f : ℚ⁺ → ℚ)
  where

  subtype-approximation-of-zero-ℚ : Prop lzero
  subtype-approximation-of-zero-ℚ =
    Π-Prop
      ( ℚ⁺)
      ( λ ε → leq-ℚ-Prop (rational-abs-ℚ (f ε)) (rational-ℚ⁺ ε))

  is-approximation-of-zero-ℚ : UU lzero
  is-approximation-of-zero-ℚ =
    type-Prop subtype-approximation-of-zero-ℚ

approximation-of-zero-ℚ : UU lzero
approximation-of-zero-ℚ = type-subtype subtype-approximation-of-zero-ℚ

module _
  (f : approximation-of-zero-ℚ)
  where

  map-approximation-of-zero-ℚ : ℚ⁺ → ℚ
  map-approximation-of-zero-ℚ = pr1 f

  is-approximation-of-zero-map-approximation-of-zero-ℚ :
    is-approximation-of-zero-ℚ map-approximation-of-zero-ℚ
  is-approximation-of-zero-map-approximation-of-zero-ℚ = pr2 f
```

### The type of rational Cauchy approximations converging to zero

```agda
zero-limit-cauchy-approximation-ℚ : UU lzero
zero-limit-cauchy-approximation-ℚ =
  type-subtype
    ( λ f →
      is-limit-cauchy-approximation-prop-Metric-Space
        metric-space-ℚ
        f
        zero-ℚ)

module _
  (f : zero-limit-cauchy-approximation-ℚ)
  where

  approximation-zero-limit-cauchy-approximation-ℚ :
    cauchy-approximation-ℚ
  approximation-zero-limit-cauchy-approximation-ℚ = pr1 f

  map-zero-limit-cauchy-approximation-ℚ : ℚ⁺ → ℚ
  map-zero-limit-cauchy-approximation-ℚ =
    map-cauchy-approximation-ℚ approximation-zero-limit-cauchy-approximation-ℚ

  is-cauchy-map-zero-limit-cauchy-approximation-ℚ :
    is-cauchy-approximation-Metric-Space
      metric-space-ℚ
      map-zero-limit-cauchy-approximation-ℚ
  is-cauchy-map-zero-limit-cauchy-approximation-ℚ =
    is-cauchy-map-cauchy-approximation-ℚ
      approximation-zero-limit-cauchy-approximation-ℚ

  is-zero-limit-approximation-zero-limit-cauchy-approximation-ℚ :
    is-limit-cauchy-approximation-Metric-Space
      metric-space-ℚ
      approximation-zero-limit-cauchy-approximation-ℚ
      zero-ℚ
  is-zero-limit-approximation-zero-limit-cauchy-approximation-ℚ = pr2 f
```

## Properties

### The type of rational approximations of zero is equivalent to the type of Cauchy approximations converging to zero

```agda
module _
  (f : ℚ⁺ → ℚ)
  (is-approximation-of-zero-f : is-approximation-of-zero-ℚ f)
  where

  abstract
    is-cauchy-approximation-is-approximation-of-zero-ℚ :
      is-cauchy-approximation-Metric-Space
        metric-space-ℚ
        f
    is-cauchy-approximation-is-approximation-of-zero-ℚ ε δ =
      neighborhood-leq-dist-ℚ
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
            ( is-approximation-of-zero-f ε)
            ( is-approximation-of-zero-f δ))
          ( leq-dist-add-abs-ℚ (f ε) (f δ)))

  cauchy-approximation-is-approximation-of-zero-ℚ :
    cauchy-approximation-ℚ
  cauchy-approximation-is-approximation-of-zero-ℚ =
    (f , is-cauchy-approximation-is-approximation-of-zero-ℚ)

  abstract
    is-zero-limit-is-approximation-of-zero-ℚ :
      is-limit-cauchy-approximation-Metric-Space
        metric-space-ℚ
        cauchy-approximation-is-approximation-of-zero-ℚ
        zero-ℚ
    is-zero-limit-is-approximation-of-zero-ℚ ε δ =
      neighborhood-leq-dist-ℚ
        ( ε +ℚ⁺ δ)
        ( f ε)
        ( zero-ℚ)
        ( transitive-leq-ℚ
          ( rational-abs-ℚ
            ( f ε -ℚ zero-ℚ))
          ( rational-ℚ⁺ ε)
          ( rational-ℚ⁺ (ε +ℚ⁺ δ))
          ( leq-le-ℚ⁺ {ε} {ε +ℚ⁺ δ} (le-left-add-ℚ⁺ ε δ))
          ( inv-tr
            ( λ y → leq-ℚ (rational-ℚ⁰⁺ y) (rational-ℚ⁺ ε))
              ( right-zero-law-dist-ℚ
              ( f ε))
            ( is-approximation-of-zero-f ε)))

module _
  (f : approximation-of-zero-ℚ)
  where

  cauchy-approximation-of-zero-ℚ : cauchy-approximation-ℚ
  cauchy-approximation-of-zero-ℚ =
    cauchy-approximation-is-approximation-of-zero-ℚ
      ( map-approximation-of-zero-ℚ f)
      ( is-approximation-of-zero-map-approximation-of-zero-ℚ f)

  is-zero-limit-cauchy-approximation-of-zero-ℚ :
    is-limit-cauchy-approximation-Metric-Space
      metric-space-ℚ
      cauchy-approximation-of-zero-ℚ
      zero-ℚ
  is-zero-limit-cauchy-approximation-of-zero-ℚ =
    is-zero-limit-is-approximation-of-zero-ℚ
      ( map-approximation-of-zero-ℚ f)
      ( is-approximation-of-zero-map-approximation-of-zero-ℚ f)

  zero-limit-cauchy-approximation-of-zero-ℚ : zero-limit-cauchy-approximation-ℚ
  zero-limit-cauchy-approximation-of-zero-ℚ =
    cauchy-approximation-of-zero-ℚ ,
    is-zero-limit-cauchy-approximation-of-zero-ℚ

module _
  ( f : cauchy-approximation-ℚ)
  ( L :
    is-limit-cauchy-approximation-Metric-Space
      metric-space-ℚ
      f
      zero-ℚ)
  where

  abstract
    is-approximation-is-zero-limit-cauchy-approximation-ℚ :
      is-approximation-of-zero-ℚ (map-cauchy-approximation-ℚ f)
    is-approximation-is-zero-limit-cauchy-approximation-ℚ ε =
      tr
        ( λ y → leq-ℚ y (rational-ℚ⁺ ε))
        ( ap
          ( rational-ℚ⁰⁺)
          ( right-zero-law-dist-ℚ (map-cauchy-approximation-ℚ f ε)))
        ( leq-dist-neighborhood-ℚ
          ( ε)
          ( map-cauchy-approximation-ℚ f ε)
          ( zero-ℚ)
          ( saturated-neighborhood-Metric-Space
            ( metric-space-ℚ)
            ( ε)
            ( map-cauchy-approximation-ℚ f ε)
            ( zero-ℚ)
            ( L ε)))

  approximation-of-zero-is-zero-limit-cauchy-approximation-ℚ :
    approximation-of-zero-ℚ
  approximation-of-zero-is-zero-limit-cauchy-approximation-ℚ =
    ( map-cauchy-approximation-ℚ f) ,
    ( is-approximation-is-zero-limit-cauchy-approximation-ℚ)

approximation-of-zero-limit-cauchy-approximation-ℚ :
  zero-limit-cauchy-approximation-ℚ → approximation-of-zero-ℚ
approximation-of-zero-limit-cauchy-approximation-ℚ =
  rec-Σ approximation-of-zero-is-zero-limit-cauchy-approximation-ℚ

section-zero-limit-cauchy-approximation-of-zero-ℚ :
  section zero-limit-cauchy-approximation-of-zero-ℚ
section-zero-limit-cauchy-approximation-of-zero-ℚ =
  ( approximation-of-zero-limit-cauchy-approximation-ℚ) ,
  ( λ f →
    eq-type-subtype
      ( λ h →
        is-limit-cauchy-approximation-prop-Metric-Space
          metric-space-ℚ
          h
          zero-ℚ)
      ( eq-type-subtype
        ( is-cauchy-approximation-prop-Metric-Space metric-space-ℚ)
        ( refl)))

retraction-zero-limit-cauchy-approximation-of-zero-ℚ :
  retraction zero-limit-cauchy-approximation-of-zero-ℚ
retraction-zero-limit-cauchy-approximation-of-zero-ℚ =
  ( approximation-of-zero-limit-cauchy-approximation-ℚ) ,
  ( λ f →
    eq-type-subtype
      ( subtype-approximation-of-zero-ℚ)
      ( refl))

is-equiv-zero-limit-cauchy-approximation-of-zero-ℚ :
  is-equiv zero-limit-cauchy-approximation-of-zero-ℚ
is-equiv-zero-limit-cauchy-approximation-of-zero-ℚ =
  section-zero-limit-cauchy-approximation-of-zero-ℚ ,
  retraction-zero-limit-cauchy-approximation-of-zero-ℚ

equiv-zero-limit-cacuhy-approximation-of-zero-ℚ :
  approximation-of-zero-ℚ ≃ zero-limit-cauchy-approximation-ℚ
equiv-zero-limit-cacuhy-approximation-of-zero-ℚ =
  zero-limit-cauchy-approximation-of-zero-ℚ ,
  is-equiv-zero-limit-cauchy-approximation-of-zero-ℚ
```
