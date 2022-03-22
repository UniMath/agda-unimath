# Constant matrices

```agda
{-# OPTIONS --without-K --exact-split #-}

module linear-algebra.constant-matrices where

open import elementary-number-theory.natural-numbers using (ℕ)

open import foundation.universe-levels using (Level; UU)

open import linear-algebra.constant-vectors using (constant-vec)
open import linear-algebra.matrices using (matrix)
```

## Idea

Constant matrices are matrices in which all elements are the same.

## Definition

```agda
constant-matrix : {l : Level} {A : UU l} {m n : ℕ} → A → matrix A m n
constant-matrix a = constant-vec (constant-vec a)
```
