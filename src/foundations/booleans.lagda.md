---
title: Univalent Mathematics in Agda
---

```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module foundations.booleans where

open import foundations.levels using (lzero; UU)
```

## The booleans

```agda
data bool : UU lzero where
  true false : bool

{-# BUILTIN BOOL bool #-}
{-# BUILTIN TRUE  true  #-}
{-# BUILTIN FALSE false #-}
```

### The boolean operators

```agda
neg-bool : bool → bool
neg-bool true = false
neg-bool false = true

conjunction-bool : bool → (bool → bool)
conjunction-bool true true = true
conjunction-bool true false = false
conjunction-bool false true = false
conjunction-bool false false = false

disjunction-bool : bool → (bool → bool)
disjunction-bool true true = true
disjunction-bool true false = true
disjunction-bool false true = true
disjunction-bool false false = false
```
