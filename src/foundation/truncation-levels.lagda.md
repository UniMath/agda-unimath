---
title: Univalent Mathematics in Agda
---

# Truncation levels


```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module foundation.truncation-levels where

open import foundation.levels using (UU; lzero)
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
```
