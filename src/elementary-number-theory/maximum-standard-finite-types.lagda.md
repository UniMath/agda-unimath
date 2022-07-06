---
title: Maximum on the standard finite types
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module elementary-number-theory.maximum-standard-finite-types where

open import elementary-number-theory.inequality-standard-finite-types
open import elementary-number-theory.natural-numbers using (ℕ; zero-ℕ; succ-ℕ)

open import foundation.dependent-pair-types using (_,_)
open import foundation.coproduct-types using (inl; inr)
open import foundation.unit-type using (star)

open import order-theory.least-upper-bounds-posets

open import univalent-combinatorics.standard-finite-types using (Fin)
```

## Idea

We define the operation of maximum (least upper bound) for the standard finite types.

## Definition

```agda
max-Fin : ∀ {k} → Fin k → Fin k → Fin k
max-Fin {k = succ-ℕ k} (inl x) (inl y) = inl (max-Fin x y)
max-Fin {k = succ-ℕ k} (inl x) (inr _) = inr star
max-Fin {k = succ-ℕ k} (inr _) (inl x) = inr star
max-Fin {k = succ-ℕ k} (inr _) (inr _) = inr star

max-Fin-Fin : {k : ℕ} (n : ℕ) → (Fin (succ-ℕ n) → Fin k) → Fin k
max-Fin-Fin zero-ℕ f     = f (inr star)
max-Fin-Fin (succ-ℕ n) f = max-Fin (f (inr star)) (max-Fin-Fin n (λ k → f (inl k)))
```

## Properties

### Maximum is greatest lower bound

```agda
leq-max-Fin :
  ∀ {k} (l m n : Fin k) → leq-Fin m l → leq-Fin n l → leq-Fin (max-Fin m n) l
leq-max-Fin {k = succ-ℕ k} (inl x) (inl y) (inl z) p q = leq-max-Fin x y z p q
leq-max-Fin {k = succ-ℕ k} (inr x) (inl y) (inl z) p q = star
leq-max-Fin {k = succ-ℕ k} (inr x) (inl y) (inr z) p q = star
leq-max-Fin {k = succ-ℕ k} (inr x) (inr y) (inl z) p q = star
leq-max-Fin {k = succ-ℕ k} (inr x) (inr y) (inr z) p q = star

leq-left-leq-max-Fin :
  ∀ {k} (l m n : Fin k) → leq-Fin (max-Fin m n) l → leq-Fin m l
leq-left-leq-max-Fin {succ-ℕ k} (inl x) (inl y) (inl z) p = leq-left-leq-max-Fin x y z p
leq-left-leq-max-Fin {succ-ℕ k} (inr x) (inl y) (inl z) p = star
leq-left-leq-max-Fin {succ-ℕ k} (inr x) (inl y) (inr z) p = star
leq-left-leq-max-Fin {succ-ℕ k} (inr x) (inr y) (inl z) p = star
leq-left-leq-max-Fin {succ-ℕ k} (inr x) (inr y) (inr z) p = star
leq-left-leq-max-Fin {succ-ℕ k} (inl x) (inr y) (inr z) p = p

leq-right-leq-max-Fin :
  ∀ {k} (l m n : Fin k) → leq-Fin (max-Fin m n) l → leq-Fin n l
leq-right-leq-max-Fin {succ-ℕ k} (inl x) (inl y) (inl z) p = leq-right-leq-max-Fin x y z p
leq-right-leq-max-Fin {succ-ℕ k} (inr x) (inl y) (inl z) p = star
leq-right-leq-max-Fin {succ-ℕ k} (inr x) (inl y) (inr z) p = star
leq-right-leq-max-Fin {succ-ℕ k} (inr x) (inr y) (inl z) p = star
leq-right-leq-max-Fin {succ-ℕ k} (inr x) (inr y) (inr z) p = star
leq-right-leq-max-Fin {succ-ℕ k} (inl x) (inl y) (inr z) p = p

is-least-upper-bound-max-Fin :
  ∀ {k} (m n : Fin k) →
  is-least-binary-upper-bound-Poset (fin-Poset k) m n (max-Fin m n)
is-least-upper-bound-max-Fin m n =
  ( leq-left-leq-max-Fin (max-Fin m n) m n (refl-leq-Fin (max-Fin m n)),
    leq-right-leq-max-Fin (max-Fin m n) m n (refl-leq-Fin (max-Fin m n))),
  λ x (m≤x , n≤x) → leq-max-Fin x m n m≤x n≤x
```
