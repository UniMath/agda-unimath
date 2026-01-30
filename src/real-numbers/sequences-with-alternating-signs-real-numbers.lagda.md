# Sequences with alternating signs in the real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.sequences-with-alternating-signs-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.parity-natural-numbers

open import foundation.conjunction
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import lists.sequences

open import real-numbers.alternation-sequences-real-numbers
open import real-numbers.dedekind-real-numbers
open import real-numbers.nonnegative-real-numbers
open import real-numbers.nonpositive-real-numbers
open import real-numbers.positive-and-negative-real-numbers
```

</details>

## Idea

A [sequence](lists.sequences.md) of
[real numbers](real-numbers.dedekind-real-numbers.md) has
{{#concept "alternating signs" Disambiguation="sequence of real numbers" Agda=has-alternating-signs-sequence-ℝ}}
if its elements at [even](elementary-number-theory.parity-natural-numbers.md)
indices are [nonnegative](real-numbers.nonnegative-real-numbers.md) and its
elements at odd indices are
[nonpositive](real-numbers.nonpositive-real-numbers.md).

## Definition

```agda
module _
  {l : Level}
  (u : sequence (ℝ l))
  where

  has-alternating-signs-prop-sequence-ℝ : Prop l
  has-alternating-signs-prop-sequence-ℝ =
    Π-Prop ℕ
      ( λ n →
        ( is-even-prop-ℕ n ⇒ is-nonnegative-prop-ℝ (u n)) ∧
        ( is-odd-prop-ℕ n ⇒ is-nonpositive-prop-ℝ (u n)))

  has-alternating-signs-sequence-ℝ : UU l
  has-alternating-signs-sequence-ℝ =
    type-Prop has-alternating-signs-prop-sequence-ℝ
```

## Properties

### A sequence has alternating signs if and only if its alternation is nonnegative

```agda
module _
  {l : Level}
  (u : sequence (ℝ l))
  where

  abstract
    is-nonnegative-alternation-has-alternating-signs-sequence-ℝ :
      has-alternating-signs-sequence-ℝ u →
      (n : ℕ) → is-nonnegative-ℝ (alternation-sequence-ℝ u n)
    is-nonnegative-alternation-has-alternating-signs-sequence-ℝ H n
      with is-decidable-is-even-ℕ n
    ... | inl even = pr1 (H n) even
    ... | inr odd = neg-is-nonpositive-ℝ _ (pr2 (H n) odd)

    has-alternating-signs-is-nonnegative-alternation-sequence-ℝ :
      ((n : ℕ) → is-nonnegative-ℝ (alternation-sequence-ℝ u n)) →
      has-alternating-signs-sequence-ℝ u
    pr1 (has-alternating-signs-is-nonnegative-alternation-sequence-ℝ H n) even =
      tr is-nonnegative-ℝ (eq-alternation-sequence-is-even-ℝ u n even) (H n)
    pr2 (has-alternating-signs-is-nonnegative-alternation-sequence-ℝ H n) odd =
      is-nonpositive-is-nonnegative-neg-ℝ _
        ( tr
          ( is-nonnegative-ℝ)
          ( eq-neg-alternation-sequence-is-odd-ℝ u n odd)
          ( H n))
```
