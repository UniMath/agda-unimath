# Scalar multiplication on matrices

```agda
{-# OPTIONS --without-K --exact-split #-}

module linear-algebra.scalar-multiplication-matrices where

open import elementary-number-theory.natural-numbers using (ℕ)

open import foundation.universe-levels using (Level; UU)

open import linear-algebra.matrices using (matrix)
open import linear-algebra.scalar-multiplication-vectors using (scalar-mul-vec)
```

```agda
scalar-mul-matrix :
  {l1 l2 : Level} {B : UU l1} {A : UU l2} {m n : ℕ} →
  (B → A → A) → B → matrix A m n → matrix A m n
scalar-mul-matrix μ = scalar-mul-vec (scalar-mul-vec μ)
```
