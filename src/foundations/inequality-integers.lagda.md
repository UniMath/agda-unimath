---
title: Univalent Mathematics in Agda
---

```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module foundations.inequality-integers where

open import foundations.coproduct-types using (coprod; map-coprod; inl; inr)
open import foundations.difference-integers using
  ( diff-ℤ; eq-diff-ℤ; distributive-neg-diff-ℤ; triangle-diff-ℤ)
open import foundations.empty-type using (empty)
open import foundations.functions using (id)
open import foundations.identity-types using (Id; refl; _∙_; inv; tr; ap)
open import foundations.integers using
  ( ℤ; is-nonnegative-ℤ; right-inverse-law-add-ℤ; is-zero-is-nonnegative-ℤ;
    is-nonnegative-eq-ℤ; is-nonnegative-add-ℤ; add-ℤ; neg-ℤ;
    decide-is-nonnegative-ℤ; succ-ℤ; left-successor-law-add-ℤ)
open import foundations.levels using (UU; lzero)
open import foundations.natural-numbers using (ℕ; zero-ℕ; succ-ℕ)
open import foundations.unit-type using (unit; star)
```

# Inequality on the integers

```agda
leq-ℤ : ℤ → ℤ → UU lzero
leq-ℤ x y = is-nonnegative-ℤ (diff-ℤ y x)

refl-leq-ℤ : (k : ℤ) → leq-ℤ k k
refl-leq-ℤ k = tr is-nonnegative-ℤ (inv (right-inverse-law-add-ℤ k)) star

antisymmetric-leq-ℤ : {x y : ℤ} → leq-ℤ x y → leq-ℤ y x → Id x y
antisymmetric-leq-ℤ {x} {y} H K =
  eq-diff-ℤ
    ( is-zero-is-nonnegative-ℤ K
      ( is-nonnegative-eq-ℤ (inv (distributive-neg-diff-ℤ x y)) H))

trans-leq-ℤ : (k l m : ℤ) → leq-ℤ k l → leq-ℤ l m → leq-ℤ k m
trans-leq-ℤ k l m p q =
  tr is-nonnegative-ℤ
    ( triangle-diff-ℤ m l k)
    ( is-nonnegative-add-ℤ
      ( add-ℤ m (neg-ℤ l))
      ( add-ℤ l (neg-ℤ k))
      ( q)
      ( p))

decide-leq-ℤ :
  {x y : ℤ} → coprod (leq-ℤ x y) (leq-ℤ y x)
decide-leq-ℤ {x} {y} =
  map-coprod
    ( id)
    ( is-nonnegative-eq-ℤ (distributive-neg-diff-ℤ y x))
    ( decide-is-nonnegative-ℤ {diff-ℤ y x})

succ-leq-ℤ : (k : ℤ) → leq-ℤ k (succ-ℤ k)
succ-leq-ℤ k =
  is-nonnegative-eq-ℤ
    ( inv
      ( ( left-successor-law-add-ℤ k (neg-ℤ k)) ∙
        ( ap succ-ℤ (right-inverse-law-add-ℤ k))))
    ( star)

leq-ℤ-succ-leq-ℤ : (k l : ℤ) → leq-ℤ k l → leq-ℤ k (succ-ℤ l)
leq-ℤ-succ-leq-ℤ k l p = trans-leq-ℤ k l (succ-ℤ l) p (succ-leq-ℤ l)

-- Bureaucracy

concatenate-eq-leq-eq-ℤ :
  {x' x y y' : ℤ} → Id x' x → leq-ℤ x y → Id y y' → leq-ℤ x' y'
concatenate-eq-leq-eq-ℤ refl H refl = H

concatenate-leq-eq-ℤ :
  (x : ℤ) {y y' : ℤ} → leq-ℤ x y → Id y y' → leq-ℤ x y'
concatenate-leq-eq-ℤ x H refl = H

concatenate-eq-leq-ℤ :
  {x x' : ℤ} (y : ℤ) → Id x' x → leq-ℤ x y → leq-ℤ x' y
concatenate-eq-leq-ℤ y refl H = H

-- The strict ordering on ℤ

le-ℤ : ℤ → ℤ → UU lzero
le-ℤ (inl zero-ℕ) (inl x) = empty
le-ℤ (inl zero-ℕ) (inr y) = unit
le-ℤ (inl (succ-ℕ x)) (inl zero-ℕ) = unit
le-ℤ (inl (succ-ℕ x)) (inl (succ-ℕ y)) = le-ℤ (inl x) (inl y)
le-ℤ (inl (succ-ℕ x)) (inr y) = unit
le-ℤ (inr x) (inl y) = empty
le-ℤ (inr (inl star)) (inr (inl star)) = empty
le-ℤ (inr (inl star)) (inr (inr x)) = unit
le-ℤ (inr (inr x)) (inr (inl star)) = empty
le-ℤ (inr (inr zero-ℕ)) (inr (inr zero-ℕ)) = empty
le-ℤ (inr (inr zero-ℕ)) (inr (inr (succ-ℕ y))) = unit
le-ℤ (inr (inr (succ-ℕ x))) (inr (inr zero-ℕ)) = empty
le-ℤ (inr (inr (succ-ℕ x))) (inr (inr (succ-ℕ y))) =
  le-ℤ (inr (inr x)) (inr (inr y))
```
