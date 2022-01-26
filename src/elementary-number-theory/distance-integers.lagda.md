---
title: Univalent Mathematics in Agda
---

# The distance between integers

```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module elementary-number-theory.distance-integers where

open import elementary-number-theory.absolute-value-integers using
  ( abs-ℤ; abs-neg-ℤ)
open import elementary-number-theory.difference-integers using
  ( diff-ℤ; left-zero-law-diff-ℤ; right-zero-law-diff-ℤ; diff-succ-ℤ)
open import elementary-number-theory.distance-natural-numbers using (dist-ℕ)
open import foundation.identity-types using (Id; refl; _∙_; inv; ap; ap-binary)
open import elementary-number-theory.integers using
  ( ℤ; zero-ℤ; int-ℕ; succ-int-ℕ)
open import elementary-number-theory.natural-numbers using (ℕ; zero-ℕ; succ-ℕ)
```

# Distance between integers

```agda
dist-ℤ : ℤ → ℤ → ℕ
dist-ℤ x y = abs-ℤ (diff-ℤ x y)

ap-dist-ℤ :
  {x x' y y' : ℤ} (p : Id x x') (q : Id y y') → Id (dist-ℤ x y) (dist-ℤ x' y')
ap-dist-ℤ p q = ap-binary dist-ℤ p q

left-zero-law-dist-ℤ : (x : ℤ) → Id (dist-ℤ zero-ℤ x) (abs-ℤ x)
left-zero-law-dist-ℤ x = ap abs-ℤ (left-zero-law-diff-ℤ x) ∙ abs-neg-ℤ x

right-zero-law-dist-ℤ : (x : ℤ) → Id (dist-ℤ x zero-ℤ) (abs-ℤ x)
right-zero-law-dist-ℤ x = ap abs-ℤ (right-zero-law-diff-ℤ x)

dist-int-ℕ :
  (x y : ℕ) → Id (dist-ℤ (int-ℕ x) (int-ℕ y)) (dist-ℕ x y)
dist-int-ℕ zero-ℕ zero-ℕ = refl
dist-int-ℕ zero-ℕ (succ-ℕ y) = left-zero-law-dist-ℤ (int-ℕ (succ-ℕ y))
dist-int-ℕ (succ-ℕ x) zero-ℕ = right-zero-law-dist-ℤ (int-ℕ (succ-ℕ x))
dist-int-ℕ (succ-ℕ x) (succ-ℕ y) =
  ( ( ap-dist-ℤ (inv (succ-int-ℕ x)) (inv (succ-int-ℕ y))) ∙
    ( ap abs-ℤ (diff-succ-ℤ (int-ℕ x) (int-ℕ y)))) ∙
  ( dist-int-ℕ x y)
```
