# Maximum on the natural numbers

```agda
{-# OPTIONS --without-K --exact-split #-}

module elementary-number-theory.maximum-natural-numbers where

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

# Maximum on the natural numbers

```agda
max-ℕ : ℕ → (ℕ → ℕ)
max-ℕ 0 n = n
max-ℕ (succ-ℕ m) 0 = succ-ℕ m
max-ℕ (succ-ℕ m) (succ-ℕ n) = succ-ℕ (max-ℕ m n)

leq-max-ℕ :
  (k m n : ℕ) → m ≤-ℕ k → n ≤-ℕ k → (max-ℕ m n) ≤-ℕ k
leq-max-ℕ zero-ℕ zero-ℕ zero-ℕ H K = star
leq-max-ℕ (succ-ℕ k) zero-ℕ zero-ℕ H K = star
leq-max-ℕ (succ-ℕ k) zero-ℕ (succ-ℕ n) H K = K
leq-max-ℕ (succ-ℕ k) (succ-ℕ m) zero-ℕ H K = H
leq-max-ℕ (succ-ℕ k) (succ-ℕ m) (succ-ℕ n) H K = leq-max-ℕ k m n H K

leq-left-leq-max-ℕ :
  (k m n : ℕ) → (max-ℕ m n) ≤-ℕ k → m ≤-ℕ k
leq-left-leq-max-ℕ k zero-ℕ zero-ℕ H = star
leq-left-leq-max-ℕ k zero-ℕ (succ-ℕ n) H = star
leq-left-leq-max-ℕ k (succ-ℕ m) zero-ℕ H = H
leq-left-leq-max-ℕ (succ-ℕ k) (succ-ℕ m) (succ-ℕ n) H =
  leq-left-leq-max-ℕ k m n H

leq-right-leq-max-ℕ :
  (k m n : ℕ) → (max-ℕ m n) ≤-ℕ k → n ≤-ℕ k
leq-right-leq-max-ℕ k zero-ℕ zero-ℕ H = star
leq-right-leq-max-ℕ k zero-ℕ (succ-ℕ n) H = H
leq-right-leq-max-ℕ k (succ-ℕ m) zero-ℕ H = star
leq-right-leq-max-ℕ (succ-ℕ k) (succ-ℕ m) (succ-ℕ n) H =
  leq-right-leq-max-ℕ k m n H

max-Fin-ℕ : (n : ℕ) → (Fin n → ℕ) → ℕ
max-Fin-ℕ zero-ℕ f = zero-ℕ
max-Fin-ℕ (succ-ℕ n) f = max-ℕ (f (inr star)) (max-Fin-ℕ n (λ k → f (inl k)))
```
