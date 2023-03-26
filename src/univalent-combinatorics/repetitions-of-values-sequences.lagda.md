# Repetitions of values in sequences

```agda
module univalent-combinatorics.repetitions-of-values-sequences where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.decidable-types

open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.negation
open import foundation.pairs-of-distinct-elements
open import foundation.repetitions-of-values
open import foundation.repetitions-sequences
open import foundation.sequences
open import foundation.universe-levels

open import univalent-combinatorics.counting
open import univalent-combinatorics.equality-standard-finite-types
open import univalent-combinatorics.standard-finite-types
```

</details>

## Properties

```agda
is-decidable-is-ordered-repetition-of-values-ℕ-Fin :
  (k : ℕ) (f : ℕ → Fin k) (x : ℕ) → is-decidable (is-ordered-repetition-of-values-ℕ f x)
is-decidable-is-ordered-repetition-of-values-ℕ-Fin k f x = {!!}

{-
  is-decidable-strictly-bounded-Σ-ℕ' x
    ( λ y → Id (f y) (f x))
    ( λ y → has-decidable-equality-Fin k (f y) (f x))
-}


is-decidable-is-ordered-repetition-of-values-ℕ-count :
  {l : Level} {A : UU l} (e : count A) (f : ℕ → A) (x : ℕ) →
  is-decidable (is-ordered-repetition-of-values-ℕ f x)
is-decidable-is-ordered-repetition-of-values-ℕ-count e f x = {!!}

{-
  is-decidable-strictly-bounded-Σ-ℕ' x
    ( λ y → Id (f y) (f x))
    ( λ y → has-decidable-equality-count e (f y) (f x))
  -}
```
