# Skipping an element in a standard finite type

```agda
{-# OPTIONS --without-K --exact-split #-}

module elementary-number-theory.skipping-element-standard-finite-type where

open import elementary-number-theory.equality-standard-finite-types using
  ( is-set-Fin)
open import elementary-number-theory.natural-numbers using (ℕ; zero-ℕ; succ-ℕ)
open import elementary-number-theory.standard-finite-types using
  ( Fin)

open import foundation.coproduct-types using (inl; inr)
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.embeddings using (is-emb; _↪_)
open import foundation.equality-coproduct-types using (is-emb-inl)
open import foundation.identity-types using (ap; refl)
open import foundation.injective-maps using
  ( is-injective; is-injective-is-emb; is-emb-is-injective)
open import foundation.unit-type using (star; unit)
```

```agda
skip-Fin :
  {k : ℕ} → Fin (succ-ℕ k) → Fin k → Fin (succ-ℕ k)
skip-Fin {succ-ℕ k} (inl x) (inl y) = inl (skip-Fin x y)
skip-Fin {succ-ℕ k} (inl x) (inr y) = inr star
skip-Fin {succ-ℕ k} (inr x) y = inl y

abstract
  is-injective-skip-Fin :
    {k : ℕ} (x : Fin (succ-ℕ k)) → is-injective (skip-Fin x)
  is-injective-skip-Fin {succ-ℕ k} (inl x) {inl y} {inl z} p =
    ap ( inl)
       ( is-injective-skip-Fin x
         ( is-injective-is-emb (is-emb-inl (Fin (succ-ℕ k)) unit) p))
  is-injective-skip-Fin {succ-ℕ k} (inl x) {inr star} {inr star} p = refl
  is-injective-skip-Fin {succ-ℕ k} (inr star) {y} {z} p =
    is-injective-is-emb (is-emb-inl (Fin (succ-ℕ k)) unit) p

abstract
  is-emb-skip-Fin :
    {k : ℕ} (x : Fin (succ-ℕ k)) → is-emb (skip-Fin x)
  is-emb-skip-Fin {k} x =
    is-emb-is-injective
      ( is-set-Fin (succ-ℕ k))
      ( is-injective-skip-Fin x)

emb-skip-Fin : {k : ℕ} (x : Fin (succ-ℕ k)) → Fin k ↪ Fin (succ-ℕ k)
pr1 (emb-skip-Fin x) = skip-Fin x
pr2 (emb-skip-Fin x) = is-emb-skip-Fin x
```
