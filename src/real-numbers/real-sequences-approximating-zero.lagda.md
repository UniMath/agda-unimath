# Real sequences approximating zero

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.real-sequences-approximating-zero where
```

<details><summary>Imports</summary>

```agda
open import metric-spaces.limits-of-sequences-metric-spaces
open import lists.sequences
open import foundation.identity-types
open import real-numbers.absolute-value-real-numbers
open import elementary-number-theory.nonnegative-rational-numbers
open import foundation.action-on-identifications-functions
open import metric-spaces.metric-space-of-rational-numbers
open import elementary-number-theory.absolute-value-rational-numbers
open import real-numbers.inequality-real-numbers
open import real-numbers.similarity-real-numbers
open import foundation.function-types
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.distance-rational-numbers
open import elementary-number-theory.natural-numbers
open import logic.functoriality-existential-quantification
open import order-theory.large-posets
open import foundation.existential-quantification
open import real-numbers.rational-real-numbers
open import real-numbers.distance-real-numbers
open import foundation.dependent-pair-types
open import foundation.universe-levels
open import real-numbers.distance-real-numbers
open import real-numbers.raising-universe-levels-real-numbers
open import real-numbers.dedekind-real-numbers
open import foundation.propositions
open import metric-spaces.rational-sequences-approximating-zero
open import real-numbers.metric-space-of-real-numbers
```

</details>

## Idea

A [sequence](lists.sequences.md) of
[real numbers](real-numbers.dedekind-real-numbers.md) is an
{{#concept "approximation of zero" Disambiguation="sequence of real numbers" Agda=zero-limit-sequence-ℝ}}
if it [converges](metric-spaces.limits-of-sequences-metric-spaces.md) to 0 in
the
[standard metric space of real numbers](real-numbers.metric-space-of-real-numbers.md).

## Definition

```agda
is-zero-limit-prop-sequence-ℝ : {l : Level} → sequence (ℝ l) → Prop l
is-zero-limit-prop-sequence-ℝ {l} σ =
  is-limit-prop-sequence-Metric-Space
    ( metric-space-ℝ l)
    ( σ)
    ( raise-ℝ l zero-ℝ)

is-zero-limit-sequence-ℝ : {l : Level} → sequence (ℝ l) → UU l
is-zero-limit-sequence-ℝ σ = type-Prop (is-zero-limit-prop-sequence-ℝ σ)
```

## Properties

### If the absolute value of a sequence of reals is bounded by a rational approximation of zero, the sequence of reals is an approximation of zero

```agda
abstract
  is-zero-limit-sequence-leq-abs-rational-zero-limit-sequence-ℝ :
    {l : Level} (a : sequence (ℝ l)) (b : zero-limit-sequence-ℚ) →
    ((n : ℕ) → leq-ℝ (abs-ℝ (a n)) (real-ℚ (seq-zero-limit-sequence-ℚ b n))) →
    is-zero-limit-sequence-ℝ a
  is-zero-limit-sequence-leq-abs-rational-zero-limit-sequence-ℝ
    {l} a (b , lim-b=0) H =
    let
      open inequality-reasoning-Large-Poset ℝ-Large-Poset
    in
      map-tot-exists
        ( λ μ is-mod-μ ε n με≤n →
          neighborhood-dist-ℝ
            ( ε)
            ( a n)
            ( raise-ℝ l zero-ℝ)
            ( chain-of-inequalities
              dist-ℝ (a n) (raise-ℝ l zero-ℝ)
              ≤ dist-ℝ (a n) zero-ℝ
                by
                  leq-sim-ℝ _ _
                    ( preserves-dist-right-sim-ℝ
                      ( symmetric-sim-ℝ (sim-raise-ℝ l zero-ℝ)))
              ≤ abs-ℝ (a n)
                by leq-eq-ℝ _ _ (right-zero-law-dist-ℝ (a n))
              ≤ real-ℚ (b n)
                by H n
              ≤ real-ℚ (rational-abs-ℚ (b n))
                by preserves-leq-real-ℚ _ _ (leq-abs-ℚ (b n))
              ≤ real-ℚ (rational-dist-ℚ (b n) zero-ℚ)
                by
                  leq-eq-ℝ _ _
                    ( ap
                      ( real-ℚ ∘ rational-ℚ⁰⁺)
                      ( inv (right-zero-law-dist-ℚ (b n))))
              ≤ real-ℚ⁺ ε
                by
                  preserves-leq-real-ℚ _ _
                    ( leq-dist-neighborhood-ℚ ε _ _ (is-mod-μ ε n με≤n))))
      ( lim-b=0)
```
