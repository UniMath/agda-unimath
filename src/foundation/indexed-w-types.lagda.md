---
title: Indexed W-types
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation.indexed-w-types where

open import foundation.universe-levels using (Level; UU; _â_)
```

```agda
data
  iğ
    {l1 l2 l3 : Level} (I : UU l1) (A : I â UU l2) (B : (i : I) â A i â UU l3)
    (f : (i : I) (x : A i) â B i x â I) (i : I) :
    UU (l2 â l3) where
  tree-iğ : (x : A i) (Î± : (y : B i x) â iğ I A B f (f i x y)) â iğ I A B f i
```
