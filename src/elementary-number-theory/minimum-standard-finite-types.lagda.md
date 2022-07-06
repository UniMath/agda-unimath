---
title: Minimum on the standard finite types
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module elementary-number-theory.minimum-standard-finite-types where

open import elementary-number-theory.inequality-standard-finite-types
open import elementary-number-theory.natural-numbers using (ℕ; zero-ℕ; succ-ℕ)

open import foundation.dependent-pair-types using (_,_)
open import foundation.coproduct-types using (inl; inr)
open import foundation.unit-type using (star)

open import order-theory.greatest-lower-bounds-posets

open import univalent-combinatorics.standard-finite-types using (Fin)
```

## Idea

We define the operation of minimum (greatest lower bound) for the standard finite types.

## Definition

```agda
min-Fin : ∀ {k} → Fin k → Fin k → Fin k
min-Fin {k = succ-ℕ k} (inl x) (inl y) = inl (min-Fin x y)
min-Fin {k = succ-ℕ k} (inl x) (inr _) = inl x
min-Fin {k = succ-ℕ k} (inr _) (inl x) = inl x
min-Fin {k = succ-ℕ k} (inr _) (inr _) = inr star

min-Fin-Fin : {k : ℕ} (n : ℕ) → (Fin (succ-ℕ n) → Fin k) → Fin k
min-Fin-Fin zero-ℕ f     = f (inr star)
min-Fin-Fin (succ-ℕ n) f = min-Fin (f (inr star)) (min-Fin-Fin n (λ k → f (inl k)))
```

## Properties

### Minimum is a greatest lower bound

We prove that `min-Fin` is a greatest lower bound of its two arguments by showing that `min(m,n) ≤ x` is equivalent to `(m ≤ x) ∧ (n ≤ x)`, in components. By reflexivity of `≤`, we compute that `min(m,n) ≤ m` (and correspondingly for `n`).

```agda
leq-min-Fin :
  ∀ {k} (l m n : Fin k) → leq-Fin l m → leq-Fin l n → leq-Fin l (min-Fin m n)
leq-min-Fin {k = succ-ℕ k} (inl x) (inl y) (inl z) p q = leq-min-Fin x y z p q
leq-min-Fin {k = succ-ℕ k} (inl x) (inl y) (inr z) p q = p
leq-min-Fin {k = succ-ℕ k} (inl x) (inr y) (inl z) p q = q
leq-min-Fin {k = succ-ℕ k} (inl x) (inr y) (inr z) p q = star
leq-min-Fin {k = succ-ℕ k} (inr x) (inr y) (inr z) p q = star

leq-left-leq-min-Fin :
  ∀ {k} (l m n : Fin k) → leq-Fin l (min-Fin m n) → leq-Fin l m
leq-left-leq-min-Fin {succ-ℕ k} (inl x) (inl y) (inl z) p = leq-left-leq-min-Fin x y z p
leq-left-leq-min-Fin {succ-ℕ k} (inl x) (inl y) (inr _) p = p
leq-left-leq-min-Fin {succ-ℕ k} (inl x) (inr _) (inl _) p = star
leq-left-leq-min-Fin {succ-ℕ k} (inl x) (inr _) (inr _) p = star
leq-left-leq-min-Fin {succ-ℕ k} (inr _) (inl y) (inr _) p = p
leq-left-leq-min-Fin {succ-ℕ k} (inr _) (inr _) (inl _) p = star
leq-left-leq-min-Fin {succ-ℕ k} (inr _) (inr _) (inr _) p = star

leq-right-leq-min-Fin :
  ∀ {k} (l m n : Fin k) → leq-Fin l (min-Fin m n) → leq-Fin l n
leq-right-leq-min-Fin {succ-ℕ k} (inl x) (inl x₁) (inl x₂) p = leq-right-leq-min-Fin x x₁ x₂ p
leq-right-leq-min-Fin {succ-ℕ k} (inl x) (inl x₁) (inr x₂) p = star
leq-right-leq-min-Fin {succ-ℕ k} (inl x) (inr x₁) (inl x₂) p = p
leq-right-leq-min-Fin {succ-ℕ k} (inl x) (inr x₁) (inr x₂) p = star
leq-right-leq-min-Fin {succ-ℕ k} (inr x) (inr x₁) (inr x₂) p = star
leq-right-leq-min-Fin {succ-ℕ k} (inr x) (inl x₁) (inl x₂) p = p
leq-right-leq-min-Fin {succ-ℕ k} (inr x) (inr x₁) (inl x₂) p = p

is-greatest-lower-bound-min-Fin :
  ∀ {k} (l m : Fin k)
  → is-greatest-binary-lower-bound-Poset (fin-Poset k) l m (min-Fin l m)
is-greatest-lower-bound-min-Fin l m =
  ( leq-left-leq-min-Fin (min-Fin l m) l m (refl-leq-Fin (min-Fin l m)),
    leq-right-leq-min-Fin (min-Fin l m) l m (refl-leq-Fin (min-Fin l m))),
  λ x (x≤l , x≤m) → leq-min-Fin x l m x≤l x≤m
```
