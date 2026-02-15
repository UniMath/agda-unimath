# Adjoining indices to boolean sequences

```agda
module set-theory.adjoining-indices-boolean-sequences where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.equality-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.booleans
open import foundation.coproduct-types
open import foundation.decidable-types
open import foundation.empty-types
open import foundation.identity-types
open import foundation.negated-equality
```

</details>

## Idea

Given a boolean sequence `χ : ℕ → bool` and an index `n`, we may change the
value at `n` to be true, leaving all other values unchanged.

## Definitions

```agda
force-true-at-sequence-bool :
  (ℕ → bool) → ℕ → ℕ → bool
force-true-at-sequence-bool χ n m =
  rec-coproduct (λ _ → true) (λ _ → χ m) (has-decidable-equality-ℕ m n)
```

## Properties

```agda
abstract
  eq-force-true-at-eq-sequence-bool :
    (χ : ℕ → bool) (n m : ℕ) →
    m ＝ n → force-true-at-sequence-bool χ n m ＝ true
  eq-force-true-at-eq-sequence-bool χ n m =
    ind-coproduct
      ( λ d → m ＝ n → rec-coproduct (λ _ → true) (λ _ → χ m) d ＝ true)
      ( λ _ _ → refl)
      ( λ q p → ex-falso (q p))
      ( has-decidable-equality-ℕ m n)

  is-true-force-true-at-sequence-bool :
    (χ : ℕ → bool) (n m : ℕ) →
    is-true (force-true-at-sequence-bool χ n m) →
    (m ＝ n) + is-true (χ m)
  is-true-force-true-at-sequence-bool χ n m =
    ind-coproduct
      ( λ d →
        is-true (rec-coproduct (λ _ → true) (λ _ → χ m) d) →
        (m ＝ n) + is-true (χ m))
      ( λ p _ → inl p)
      ( λ _ H' → inr H')
      ( has-decidable-equality-ℕ m n)

  is-false-force-true-at-sequence-bool :
    (χ : ℕ → bool) (n m : ℕ) →
    m ≠ n →
    is-false (χ m) →
    is-false (force-true-at-sequence-bool χ n m)
  is-false-force-true-at-sequence-bool χ n m =
    ind-coproduct
      ( λ d →
        m ≠ n →
        is-false (χ m) →
        is-false (rec-coproduct (λ _ → true) (λ _ → χ m) d))
      ( λ p neq' _ → ex-falso (neq' p))
      ( λ _ _ χm=false' → χm=false')
      ( has-decidable-equality-ℕ m n)

  is-true-force-true-at-self-sequence-bool :
    (χ : ℕ → bool) (n : ℕ) →
    is-true (force-true-at-sequence-bool χ n n)
  is-true-force-true-at-self-sequence-bool χ n =
    ind-coproduct
      ( λ d → is-true (rec-coproduct (λ _ → true) (λ _ → χ n) d))
      ( λ _ → refl)
      ( λ n≠n → ex-falso (n≠n refl))
      ( has-decidable-equality-ℕ n n)

  eq-force-true-at-neq-sequence-bool :
    (χ : ℕ → bool) (n m : ℕ) →
    m ≠ n → force-true-at-sequence-bool χ n m ＝ χ m
  eq-force-true-at-neq-sequence-bool χ n m =
    ind-coproduct
      ( λ d → m ≠ n → rec-coproduct (λ _ → true) (λ _ → χ m) d ＝ χ m)
      ( λ p m≠n' → ex-falso (m≠n' p))
      ( λ _ _ → refl)
      ( has-decidable-equality-ℕ m n)
```
