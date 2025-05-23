# Rational sequences approximating zero

```agda
{-# OPTIONS --lossy-unification #-}

module metric-spaces.rational-sequences-approximating-zero where
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
open import foundation.sequences
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import metric-spaces.cauchy-approximations-metric-spaces
open import metric-spaces.convergent-cauchy-approximations-metric-spaces
open import metric-spaces.limits-of-cauchy-approximations-premetric-spaces
open import metric-spaces.limits-of-sequences-metric-spaces
open import metric-spaces.metric-space-of-rational-numbers
open import metric-spaces.metric-spaces
open import metric-spaces.rational-cauchy-approximations
open import metric-spaces.sequences-metric-spaces
```

</details>

## Idea

A [sequence](foundation.sequences.md) of
[rational numbers](elementary-number-theory.rational-numbers.md) is a
{{#concept "zero approximation" Disambiguation="sequence of rational numbers" Agda=zero-approximation-sequence-ℚ}}
if it [converges](metric-spaces.limits-of-sequences-metric-spaces.md) to
zero in the
[standard metric space of rational numbers](metric-spaces.metric-space-of-rational-numbers.md).

## Definitions

```agda
is-zero-approximation-prop-sequence-ℚ : sequence ℚ → Prop lzero
is-zero-approximation-prop-sequence-ℚ u =
  is-limit-prop-sequence-Metric-Space
    metric-space-leq-ℚ
    u
    zero-ℚ

is-zero-approximation-sequence-ℚ : sequence ℚ → UU lzero
is-zero-approximation-sequence-ℚ u =
  type-Prop (is-zero-approximation-prop-sequence-ℚ u)

zero-approximation-sequence-ℚ : UU lzero
zero-approximation-sequence-ℚ =
  type-subtype is-zero-approximation-prop-sequence-ℚ

module _
  (u : zero-approximation-sequence-ℚ)
  where

  seq-zero-approximation-sequence-ℚ : sequence ℚ
  seq-zero-approximation-sequence-ℚ = pr1 u

  is-zero-limit-seq-zero-approximation-sequence-ℚ :
    is-limit-sequence-Metric-Space
      ( metric-space-leq-ℚ)
      ( seq-zero-approximation-sequence-ℚ)
      ( zero-ℚ)
  is-zero-limit-seq-zero-approximation-sequence-ℚ = pr2 u
```
