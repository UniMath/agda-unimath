---
title: Truncated equality
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation.truncated-equality where

open import foundation.identity-types using (_＝_)
open import foundation.truncated-types using (Truncated-Type)
open import foundation.truncation-levels using (𝕋)
open import foundation.truncations using (trunc)
open import foundation.universe-levels using (Level; UU)
```

## Definition

```agda
trunc-eq : {l : Level} (k : 𝕋) {A : UU l} → A → A → Truncated-Type l k
trunc-eq k x y = trunc k (x ＝ y)
```

## Properties
