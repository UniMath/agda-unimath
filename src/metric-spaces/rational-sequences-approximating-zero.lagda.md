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
[rational numbers](elementary-number-theory.rational-numbers.md) is an
{{#concept "approximation of zero" Disambiguation="sequence of rational numbers" Agda=zero-limit-sequence-ℚ}}
if it [converges](metric-spaces.limits-of-sequences-metric-spaces.md) to 0 in
the
[standard metric space of rational numbers](metric-spaces.metric-space-of-rational-numbers.md).

## Definitions

```agda
is-zero-limit-prop-sequence-ℚ : sequence ℚ → Prop lzero
is-zero-limit-prop-sequence-ℚ u =
  is-limit-prop-sequence-Metric-Space
    metric-space-leq-ℚ
    u
    zero-ℚ

zero-limit-sequence-ℚ : UU lzero
zero-limit-sequence-ℚ =
  type-subtype is-zero-limit-prop-sequence-ℚ

module _
  (u : zero-limit-sequence-ℚ)
  where

  seq-zero-limit-sequence-ℚ : sequence ℚ
  seq-zero-limit-sequence-ℚ = pr1 u

  is-zero-limit-seq-zero-limit-sequence-ℚ :
    is-limit-sequence-Metric-Space
      ( metric-space-leq-ℚ)
      ( seq-zero-limit-sequence-ℚ)
      ( zero-ℚ)
  is-zero-limit-seq-zero-limit-sequence-ℚ = pr2 u
```
