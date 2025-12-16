# Sequences with alternating signs in the real numbers

```agda
module real-numbers.sequences-with-alternating-signs-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.parity-natural-numbers
open import lists.sequences
open import real-numbers.dedekind-real-numbers
open import real-numbers.positive-and-negative-real-numbers
open import real-numbers.alternation-sequences-real-numbers
open import real-numbers.nonnegative-real-numbers
open import foundation.propositions
open import foundation.conjunction
open import foundation.universe-levels
open import real-numbers.nonpositive-real-numbers
```

</details>

## Idea

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
