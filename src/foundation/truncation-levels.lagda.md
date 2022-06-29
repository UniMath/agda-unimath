---
title: Truncation levels
---


```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation.truncation-levels where

open import foundation-core.truncation-levels public

open import elementary-number-theory.natural-numbers using (ℕ; zero-ℕ; succ-ℕ)
```

## Properties

### Natural numbers can be converted into truncation levels

```agda
truncation-level-ℕ : ℕ → 𝕋
truncation-level-ℕ zero-ℕ = zero-𝕋
truncation-level-ℕ (succ-ℕ n) = succ-𝕋 (truncation-level-ℕ n)
```
