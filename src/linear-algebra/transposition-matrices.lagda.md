# Transposition of matrices

```agda
{-# OPTIONS --without-K --exact-split #-}

module linear-algebra.transposition-matrices where

open import elementary-number-theory.natural-numbers using (ℕ; zero-ℕ; succ-ℕ)

open import foundation.identity-types using
  ( Id; refl; ap; _∙_; ap-binary)
open import foundation.universe-levels using (Level; UU)

open import linear-algebra.functoriality-vectors using (map-vec)
open import linear-algebra.matrices using (Mat)
open import linear-algebra.vectors using (empty-vec; _∷_; head; tail; vec)
```

## Idea

The transposition of a matrix is the operation that turns rows into columns and columns into rows.

## Definition

```agda
transpose-matrix :
  {l : Level} → {K : UU l} → {m n : ℕ} → Mat K m n → Mat K n m
transpose-matrix {n = zero-ℕ} x = empty-vec
transpose-matrix {n = succ-ℕ n} x =
  map-vec head x ∷ transpose-matrix (map-vec tail x)
```

## Properties

```agda
is-involution-transpose-matrix :
  {l : Level} → {K : UU l} → {m n : ℕ} →
  (x : Mat K m n) → Id x (transpose-matrix (transpose-matrix x))
is-involution-transpose-matrix {m = zero-ℕ} empty-vec = refl
is-involution-transpose-matrix {m = succ-ℕ m} (r ∷ rs) =
  ( ap (_∷_ r) (is-involution-transpose-matrix rs)) ∙
  ( ap-binary _∷_
    ( lemma-first-row r rs) (ap transpose-matrix (lemma-rest r rs)))
  where
  lemma-first-row :
    {l : Level} → {K : UU l} → {m n : ℕ} → (x : vec K n) → (xs : Mat K m n) →
    Id x (map-vec head (transpose-matrix (x ∷ xs)))
  lemma-first-row {n = zero-ℕ} empty-vec _ = refl
  lemma-first-row {n = succ-ℕ m} (k ∷ ks) xs =
    ap (_∷_ k) (lemma-first-row ks (map-vec tail xs))

  lemma-rest :
    {l : Level} → {K : UU l} → {m n : ℕ} → (x : vec K n) → (xs : Mat K m n) →
    Id (transpose-matrix xs) (map-vec tail (transpose-matrix (x ∷ xs)))
  lemma-rest {n = zero-ℕ} empty-vec xs = refl
  lemma-rest {n = succ-ℕ n} (k ∷ ks) xs =
    ap (_∷_ (map-vec head xs))
       (lemma-rest (tail (k ∷ ks)) (map-vec tail xs))
```
