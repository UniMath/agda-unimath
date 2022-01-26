---
title: Univalent Mathematics in Agda
---

# Equivalences between standard finite types

```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module elementary-number-theory.equivalences-standard-finite-types where

open import elementary-number-theory.addition-natural-numbers using (add-ℕ)
open import foundation.cartesian-product-types using (_×_)
open import foundations.coproduct-types using (coprod)
open import foundations.empty-type using (left-absorption-prod)
open import foundation.equivalences using (_≃_; id-equiv; _∘e_; inv-equiv)
open import foundations.functoriality-coproduct-types using (equiv-coprod)
open import elementary-number-theory.multiplication-natural-numbers using
  ( mul-ℕ)
open import elementary-number-theory.natural-numbers using (ℕ; zero-ℕ; succ-ℕ)
open import elementary-number-theory.standard-finite-types using (Fin)
open import foundations.type-arithmetic-coproduct-types using
  ( right-unit-law-coprod; inv-assoc-coprod; right-distributive-prod-coprod)
open import foundations.unit-type using (unit; left-unit-law-prod)
```

# Equivalences between standard finite types

```agda
coprod-Fin :
  (k l : ℕ) → coprod (Fin k) (Fin l) ≃ Fin (add-ℕ k l)
coprod-Fin k zero-ℕ = right-unit-law-coprod (Fin k)
coprod-Fin k (succ-ℕ l) =
  (equiv-coprod (coprod-Fin k l) id-equiv) ∘e inv-assoc-coprod

Fin-add-ℕ :
  (k l : ℕ) → Fin (add-ℕ k l) ≃ coprod (Fin k) (Fin l)
Fin-add-ℕ k l = inv-equiv (coprod-Fin k l)

prod-Fin : (k l : ℕ) → ((Fin k) × (Fin l)) ≃ Fin (mul-ℕ k l)
prod-Fin zero-ℕ l = left-absorption-prod (Fin l)
prod-Fin (succ-ℕ k) l =
  ( ( coprod-Fin (mul-ℕ k l) l) ∘e
    ( equiv-coprod (prod-Fin k l) left-unit-law-prod)) ∘e
  ( right-distributive-prod-coprod (Fin k) unit (Fin l))

Fin-mul-ℕ : (k l : ℕ) → (Fin (mul-ℕ k l)) ≃ ((Fin k) × (Fin l))
Fin-mul-ℕ k l = inv-equiv (prod-Fin k l)
```
