# Sublinear rational functions

```agda
{-# OPTIONS --lossy-unification #-}

module elementary-number-theory.sublinear-rational-functions where
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

open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.binary-transport
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import metric-spaces.cauchy-approximations-metric-spaces
open import metric-spaces.metric-space-of-rational-numbers
open import metric-spaces.metric-spaces
open import metric-spaces.rational-cauchy-approximations
```

</details>

## Idea

A [rational](elementary-number-theory.rational-numbers.md) map `f : ℚ → ℚ` is
{{#concept "sublinear" Disambiguation="rational map" Agda=sublinear-map-ℚ}} if
`|f ε| ≤ |ε|` for all `ε : ℚ`.

Any sublinear map is a
[rational Cauchy approximation](metric-spaces.rational-cauchy-approximations.md).

## Definitions

### Sublinear rational maps

```agda
module _
  (f : ℚ → ℚ)
  where

  is-sublinear-prop-map-ℚ : Prop lzero
  is-sublinear-prop-map-ℚ =
    Π-Prop
      ( ℚ)
      ( λ r → leq-ℚ-Prop (rational-abs-ℚ (f r)) (rational-abs-ℚ r))

  is-sublinear-map-ℚ : UU lzero
  is-sublinear-map-ℚ = type-Prop is-sublinear-prop-map-ℚ

sublinear-map-ℚ : UU lzero
sublinear-map-ℚ = type-subtype is-sublinear-prop-map-ℚ

module _
  (f : sublinear-map-ℚ)
  where

  map-sublinear-map-ℚ : ℚ → ℚ
  map-sublinear-map-ℚ = pr1 f

  is-sublinear-map-sublinear-map-ℚ :
    is-sublinear-map-ℚ map-sublinear-map-ℚ
  is-sublinear-map-sublinear-map-ℚ = pr2 f
```

## Properties

### A sublinear map defines a rational Cauchy approximation

```agda
module _
  (f : ℚ → ℚ) (is-sublinear-f : is-sublinear-map-ℚ f)
  where

  abstract
    is-cauchy-approximation-is-sublinear-map-ℚ :
      is-cauchy-approximation-Metric-Space
        metric-space-leq-ℚ
        (f ∘ rational-ℚ⁺)
    is-cauchy-approximation-is-sublinear-map-ℚ ε⁺@(ε , pos-ε) δ⁺@(δ , pos-δ) =
      neighborhood-leq-leq-dist-ℚ
        ( ε⁺ +ℚ⁺ δ⁺)
        ( f ε)
        ( f δ)
        ( tr
          ( leq-ℚ (rational-dist-ℚ (f ε) (f δ)))
          ( ap-binary
            ( add-ℚ)
            ( ap (rational-ℚ⁰⁺) (abs-rational-ℚ⁰⁺ (nonnegative-ℚ⁺ ε⁺)))
            ( ap (rational-ℚ⁰⁺) (abs-rational-ℚ⁰⁺ (nonnegative-ℚ⁺ δ⁺))))
          ( transitive-leq-ℚ
            ( rational-dist-ℚ (f ε) (f δ))
            ( rational-abs-ℚ (f ε) +ℚ (rational-abs-ℚ (f δ)))
            ( rational-abs-ℚ ε +ℚ rational-abs-ℚ δ)
            ( preserves-leq-add-ℚ
              { rational-abs-ℚ (f ε)}
              { rational-abs-ℚ ε}
              { rational-abs-ℚ (f δ)}
              { rational-abs-ℚ δ}
              ( is-sublinear-f ε)
              ( is-sublinear-f δ))
            ( leq-dist-add-abs-ℚ (f ε) (f δ))))

  cauchy-approximation-is-sublinear-map-ℚ : cauchy-approximation-ℚ
  cauchy-approximation-is-sublinear-map-ℚ =
    (f ∘ rational-ℚ⁺ , is-cauchy-approximation-is-sublinear-map-ℚ)

cauchy-sublinear-map-ℚ :
  sublinear-map-ℚ → cauchy-approximation-ℚ
cauchy-sublinear-map-ℚ f =
  cauchy-approximation-is-sublinear-map-ℚ
    ( map-sublinear-map-ℚ f)
    ( is-sublinear-map-sublinear-map-ℚ f)
```
