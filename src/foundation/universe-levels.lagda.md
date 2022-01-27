---
title: Univalent Mathematics in Agda
---

```agda
{-# OPTIONS --without-K --exact-split --safe --no-import-sorts #-}

module foundation.universe-levels where

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_) renaming (Set to UU) public
```
