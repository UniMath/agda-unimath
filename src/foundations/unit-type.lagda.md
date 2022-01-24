---
title: Univalent Mathematics in Agda
---

```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module foundations.unit-type where

open import foundations.levels using (Level; lzero; UU)
```

## The unit type

```agda
data unit : UU lzero where
  star : unit

ind-unit : {l : Level} {P : unit → UU l} → P star → ((x : unit) → P x)
ind-unit p star = p

terminal-map : {l : Level} {A : UU l} → A → unit
terminal-map a = star
```
