# Diagonal vectors

```agda
{-# OPTIONS --without-K --exact-split #-}

module linear-algebra.diagonal-vectors where

open import elementary-number-theory.natural-numbers using (ℕ; zero-ℕ; succ-ℕ)

open import foundation.universe-levels using (Level; UU)

open import linear-algebra.vectors using (vec; empty-vec; _∷_)
```

## Idea

Diagonal vectors are vectors on the diagonal, i.e., they are vectors of which all coefficients are equal.

## Definition

```agda
diagonal-vec : {l : Level} {A : UU l} {n : ℕ} → A → vec A n
diagonal-vec {n = zero-ℕ} _ = empty-vec
diagonal-vec {n = succ-ℕ n} x = x ∷ (diagonal-vec x)
```
