# Repetitions in sequences

```agda
module foundation.repetitions-sequences where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.negation
open import foundation.pairs-of-distinct-elements
open import foundation.repetitions
open import foundation.sequences
open import foundation.universe-levels
```

</details>

## Idea

A repetition in a sequence `a : ℕ → A` consists of a pair of distinct natural numbers `m` and `n` such that `a m = a n`.

## Definition

```agda
is-repetition-pair-of-distinct-elements-sequence :
  {l : Level} {A : UU l} (a : sequence A) (p : pair-of-distinct-elements ℕ) →
  UU l
is-repetition-pair-of-distinct-elements-sequence a p =
  is-repetition-pair-of-distinct-elements a p

repetition-sequence :
  {l : Level} {A : UU l} → sequence A → UU l
repetition-sequence a =
  Σ (pair-of-distinct-elements ℕ) (is-repetition-pair-of-distinct-elements a)

module _
  {l : Level} {A : UU l} (a : sequence A) (r : repetition-sequence a)
  where

  pair-of-distinct-elements-repetition-sequence :
    pair-of-distinct-elements ℕ
  pair-of-distinct-elements-repetition-sequence = pr1 r

  fst-repetition-sequence : ℕ
  fst-repetition-sequence =
    fst-pair-of-distinct-elements pair-of-distinct-elements-repetition-sequence

  snd-repetition-sequence : ℕ
  snd-repetition-sequence =
    snd-pair-of-distinct-elements pair-of-distinct-elements-repetition-sequence

  distinction-repetition-sequence :
    ¬ (fst-repetition-sequence ＝ snd-repetition-sequence)
  distinction-repetition-sequence =
    distinction-pair-of-distinct-elements
      pair-of-distinct-elements-repetition-sequence

  is-repetition-pair-of-distinct-elements-repetition-sequence :
    is-repetition-pair-of-distinct-elements a
      pair-of-distinct-elements-repetition-sequence
  is-repetition-pair-of-distinct-elements-repetition-sequence = pr2 r
```
