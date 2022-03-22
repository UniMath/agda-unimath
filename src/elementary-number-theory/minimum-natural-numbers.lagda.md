# Minimum on the natural numbers

```agda
{-# OPTIONS --without-K --exact-split #-}

module elementary-number-theory.minimum-natural-numbers where

open import elementary-number-theory.addition-natural-numbers using
  ( add-ℕ; commutative-add-ℕ; left-unit-law-add-ℕ)
open import elementary-number-theory.inequality-natural-numbers using (_≤-ℕ_)
open import elementary-number-theory.multiplication-natural-numbers using
  ( mul-ℕ; commutative-mul-ℕ; right-unit-law-mul-ℕ; right-zero-law-mul-ℕ;
    right-successor-law-mul-ℕ)
open import elementary-number-theory.natural-numbers using
  ( ℕ; zero-ℕ; succ-ℕ; is-zero-ℕ; is-zero-ℕ'; is-nonzero-ℕ;
    is-successor-is-nonzero-ℕ; is-nonzero-succ-ℕ; is-injective-succ-ℕ)

open import foundation.cartesian-product-types using (_×_)
open import foundation.coproduct-types using (coprod; inl; inr)
open import foundation.decidable-types using (is-decidable)
open import foundation.dependent-pair-types using (pair; pr1; pr2; Σ)
open import foundation.empty-types using (empty; ex-falso; is-prop-empty)
open import foundation.functions using (id; _∘_)
open import foundation.functoriality-coproduct-types using (map-coprod)
open import foundation.identity-types using (Id; refl; inv; ap; tr)
open import foundation.negation using (¬)
open import foundation.propositions using (is-prop; UU-Prop)
open import foundation.unit-type using (unit; star; is-prop-unit)
open import foundation.universe-levels using (UU; lzero)

open import univalent-combinatorics.standard-finite-types using (Fin)
```

# Minimum on the natural numbers

```agda
min-ℕ : ℕ → (ℕ → ℕ)
min-ℕ 0 n = 0
min-ℕ (succ-ℕ m) 0 = 0
min-ℕ (succ-ℕ m) (succ-ℕ n) = succ-ℕ (min-ℕ m n)

leq-min-ℕ :
  (k m n : ℕ) → k ≤-ℕ m → k ≤-ℕ n → k ≤-ℕ (min-ℕ m n)
leq-min-ℕ zero-ℕ zero-ℕ zero-ℕ H K = star
leq-min-ℕ zero-ℕ zero-ℕ (succ-ℕ n) H K = star
leq-min-ℕ zero-ℕ (succ-ℕ m) zero-ℕ H K = star
leq-min-ℕ zero-ℕ (succ-ℕ m) (succ-ℕ n) H K = star
leq-min-ℕ (succ-ℕ k) (succ-ℕ m) (succ-ℕ n) H K = leq-min-ℕ k m n H K

leq-left-leq-min-ℕ :
  (k m n : ℕ) → k ≤-ℕ (min-ℕ m n) → k ≤-ℕ m
leq-left-leq-min-ℕ zero-ℕ zero-ℕ zero-ℕ H = star
leq-left-leq-min-ℕ zero-ℕ zero-ℕ (succ-ℕ n) H = star
leq-left-leq-min-ℕ zero-ℕ (succ-ℕ m) zero-ℕ H = star
leq-left-leq-min-ℕ zero-ℕ (succ-ℕ m) (succ-ℕ n) H = star
leq-left-leq-min-ℕ (succ-ℕ k) (succ-ℕ m) (succ-ℕ n) H =
  leq-left-leq-min-ℕ k m n H

leq-right-leq-min-ℕ :
  (k m n : ℕ) → k ≤-ℕ (min-ℕ m n) → k ≤-ℕ n
leq-right-leq-min-ℕ zero-ℕ zero-ℕ zero-ℕ H = star
leq-right-leq-min-ℕ zero-ℕ zero-ℕ (succ-ℕ n) H = star
leq-right-leq-min-ℕ zero-ℕ (succ-ℕ m) zero-ℕ H = star
leq-right-leq-min-ℕ zero-ℕ (succ-ℕ m) (succ-ℕ n) H = star
leq-right-leq-min-ℕ (succ-ℕ k) (succ-ℕ m) (succ-ℕ n) H =
  leq-right-leq-min-ℕ k m n H

min-Fin-ℕ : (n : ℕ) → (Fin (succ-ℕ n) → ℕ) → ℕ
min-Fin-ℕ zero-ℕ f = f (inr star)
min-Fin-ℕ (succ-ℕ n) f = min-ℕ (f (inr star)) (min-Fin-ℕ n (λ k → f (inl k)))
```
