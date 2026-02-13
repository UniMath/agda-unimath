# Forcing boolean predicates at an index on natural numbers

```agda
module elementary-number-theory.forcing-boolean-predicates-natural-numbers where
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

Given a boolean predicate `χ : ℕ → bool` and an index `n`, we force the value at
`n` to be `true`, leaving all other values unchanged.

## Definitions

```agda
force-true-at-from-decidable-equality-ℕ :
  (n : ℕ) (χ : ℕ → bool) (m : ℕ) →
  is-decidable (m ＝ n) →
  bool
force-true-at-from-decidable-equality-ℕ n χ m (inl _) = true
force-true-at-from-decidable-equality-ℕ n χ m (inr _) = χ m

force-true-at-ℕ :
  ℕ → (ℕ → bool) → ℕ → bool
force-true-at-ℕ n χ m =
  force-true-at-from-decidable-equality-ℕ n χ m
    ( has-decidable-equality-ℕ m n)
```

## Properties

```agda
abstract
  eq-force-true-at-from-decidable-equality-inl-ℕ :
    (n : ℕ) (χ : ℕ → bool) (m : ℕ) (p : m ＝ n) →
    force-true-at-from-decidable-equality-ℕ n χ m (inl p) ＝ true
  eq-force-true-at-from-decidable-equality-inl-ℕ n χ m p = refl

  eq-force-true-at-from-decidable-equality-inr-ℕ :
    (n : ℕ) (χ : ℕ → bool) (m : ℕ) (p : m ＝ n → empty) →
    force-true-at-from-decidable-equality-ℕ n χ m (inr p) ＝ χ m
  eq-force-true-at-from-decidable-equality-inr-ℕ n χ m p = refl

  is-true-force-true-at-ℕ :
    (n : ℕ) (χ : ℕ → bool) (m : ℕ) →
    is-true (force-true-at-ℕ n χ m) →
    (m ＝ n) + is-true (χ m)
  is-true-force-true-at-ℕ n χ m =
    ind-coproduct
      ( λ d →
        is-true (force-true-at-from-decidable-equality-ℕ n χ m d) →
        (m ＝ n) + is-true (χ m))
      ( λ p _ → inl p)
      ( λ _ H' → inr H')
      ( has-decidable-equality-ℕ m n)

  is-false-force-true-at-ℕ :
    (n : ℕ) (χ : ℕ → bool) (m : ℕ) →
    m ≠ n →
    is-false (χ m) →
    is-false (force-true-at-ℕ n χ m)
  is-false-force-true-at-ℕ n χ m =
    ind-coproduct
      ( λ d →
        m ≠ n →
        is-false (χ m) →
        is-false (force-true-at-from-decidable-equality-ℕ n χ m d))
      ( λ p neq' _ → ex-falso (neq' p))
      ( λ _ _ χm=false' → χm=false')
      ( has-decidable-equality-ℕ m n)

  is-true-force-true-at-self-ℕ :
    (n : ℕ) (χ : ℕ → bool) →
    is-true (force-true-at-ℕ n χ n)
  is-true-force-true-at-self-ℕ n χ =
    ind-coproduct
      ( λ d → is-true (force-true-at-from-decidable-equality-ℕ n χ n d))
      ( λ _ → refl)
      ( λ n≠n → ex-falso (n≠n refl))
      ( has-decidable-equality-ℕ n n)

  eq-force-true-at-neq-ℕ :
    (n : ℕ) (χ : ℕ → bool) (m : ℕ) →
    m ≠ n → force-true-at-ℕ n χ m ＝ χ m
  eq-force-true-at-neq-ℕ n χ m =
    ind-coproduct
      ( λ d → m ≠ n → force-true-at-from-decidable-equality-ℕ n χ m d ＝ χ m)
      ( λ p m≠n' → ex-falso (m≠n' p))
      ( λ _ _ → refl)
      ( has-decidable-equality-ℕ m n)
```
