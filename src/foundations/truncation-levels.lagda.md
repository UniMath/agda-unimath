---
title: Univalent Mathematics in Agda
---

# Truncation levels


```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module foundations.truncation-levels where

open import foundations.levels using (UU; lzero)
open import foundations.natural-numbers using (ℕ; zero-ℕ; succ-ℕ)
```

## The type of truncation levels

```agda
data 𝕋 : UU lzero where
  neg-two-𝕋 : 𝕋
  succ-𝕋 : 𝕋 → 𝕋

neg-one-𝕋 : 𝕋
neg-one-𝕋 = succ-𝕋 neg-two-𝕋

zero-𝕋 : 𝕋
zero-𝕋 = succ-𝕋 neg-one-𝕋

one-𝕋 : 𝕋
one-𝕋 = succ-𝕋 zero-𝕋

two-𝕋 : 𝕋
two-𝕋 = succ-𝕋 one-𝕋

truncation-level-ℕ : ℕ → 𝕋
truncation-level-ℕ zero-ℕ = zero-𝕋
truncation-level-ℕ (succ-ℕ k) = succ-𝕋 (truncation-level-ℕ k)

truncation-level-minus-one-ℕ : ℕ → 𝕋
truncation-level-minus-one-ℕ zero-ℕ = neg-one-𝕋
truncation-level-minus-one-ℕ (succ-ℕ k) =
  succ-𝕋 (truncation-level-minus-one-ℕ k)

truncation-level-minus-two-ℕ : ℕ → 𝕋
truncation-level-minus-two-ℕ zero-ℕ = neg-two-𝕋
truncation-level-minus-two-ℕ (succ-ℕ k) =
  succ-𝕋 (truncation-level-minus-two-ℕ k)

add-𝕋 : 𝕋 → 𝕋 → 𝕋
add-𝕋 neg-two-𝕋 neg-two-𝕋 = neg-two-𝕋
add-𝕋 neg-two-𝕋 (succ-𝕋 neg-two-𝕋) = neg-two-𝕋
add-𝕋 neg-two-𝕋 (succ-𝕋 (succ-𝕋 y)) = y
add-𝕋 (succ-𝕋 neg-two-𝕋) neg-two-𝕋 = neg-two-𝕋
add-𝕋 (succ-𝕋 neg-two-𝕋) (succ-𝕋 y) = y
add-𝕋 (succ-𝕋 (succ-𝕋 neg-two-𝕋)) y = y
add-𝕋 (succ-𝕋 (succ-𝕋 (succ-𝕋 x))) y = succ-𝕋 (add-𝕋 (succ-𝕋 (succ-𝕋 x)) y)
```
