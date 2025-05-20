# Sublinear rational Cauchy approximations

```agda
{-# OPTIONS --lossy-unification #-}

module elementary-number-theory.sublinear-rational-cauchy-approximations where
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

open import foundation.dependent-pair-types
open import foundation.propositions
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import metric-spaces.cauchy-approximations-metric-spaces
open import metric-spaces.convergent-cauchy-approximations-metric-spaces
open import metric-spaces.metric-space-of-rational-numbers
open import metric-spaces.metric-spaces
open import metric-spaces.rational-cauchy-approximations
```

</details>

## Idea

A [rational](elementary-number-theory.rational-numbers.md) map from the
[positive rational numbers](elementary-number-theory.positive-rational-numbers.md)
`f : ℚ⁺ → ℚ` is
{{#concept "sublinear" Disambiguation="rational approximation" Agda=sublinear-approximation-ℚ}}
if `|f ε| ≤ ε` for all `ε : ℚ⁺`. Any sublinear map is a
[rational Cauchy approximation](metric-spaces.rational-cauchy-approximations.md).

## Definitions

### Sublinear rational approximations

```agda
module _
  (f : ℚ⁺ → ℚ)
  where

  is-sublinear-prop-approximation-ℚ : Prop lzero
  is-sublinear-prop-approximation-ℚ =
    Π-Prop
      ( ℚ⁺)
      ( λ ε → leq-ℚ-Prop (rational-abs-ℚ (f ε)) (rational-ℚ⁺ ε))

  is-sublinear-approximation-ℚ : UU lzero
  is-sublinear-approximation-ℚ =
    type-Prop is-sublinear-prop-approximation-ℚ

sublinear-approximation-ℚ : UU lzero
sublinear-approximation-ℚ = type-subtype is-sublinear-prop-approximation-ℚ

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

### Any sublinear map `ℚ⁺ → ℚ` is a Cauchy approximation

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

cauchy-sublinear-approximation-ℚ :
  sublinear-approximation-ℚ → cauchy-approximation-ℚ
cauchy-sublinear-approximation-ℚ f =
  cauchy-approximation-is-sublinear-approximation-ℚ
    ( map-sublinear-approximation-ℚ f)
    ( is-sublinear-map-sublinear-approximation-ℚ f)
```

### A sublinear map `ℚ⁺ → ℚ` converges to zero

```agda
module _
  (f : sublinear-approximation-ℚ)
  where

  abstract
    is-zero-limit-map-sublinear-approximation-ℚ :
      is-limit-cauchy-approximation-Metric-Space
        ( metric-space-leq-ℚ)
        ( cauchy-sublinear-approximation-ℚ f)
        ( zero-ℚ)
    is-zero-limit-map-sublinear-approximation-ℚ ε δ =
      neighborhood-leq-leq-dist-ℚ
        ( ε +ℚ⁺ δ)
        ( map-sublinear-approximation-ℚ f ε)
        ( zero-ℚ)
        ( transitive-leq-ℚ
          ( rational-abs-ℚ
            ( (map-sublinear-approximation-ℚ f ε) -ℚ zero-ℚ))
          ( rational-ℚ⁺ ε)
          ( rational-ℚ⁺ (ε +ℚ⁺ δ))
          ( leq-le-ℚ⁺ {ε} {ε +ℚ⁺ δ} (le-left-add-ℚ⁺ ε δ))
          ( inv-tr
            ( λ y → leq-ℚ (rational-ℚ⁰⁺ y) (rational-ℚ⁺ ε))
            ( right-zero-law-dist-ℚ
              ( map-sublinear-approximation-ℚ f ε))
            ( is-sublinear-map-sublinear-approximation-ℚ f ε)))
```
