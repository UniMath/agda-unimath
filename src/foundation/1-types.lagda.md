---
title: Univalent Mathematics in Agda
---

# 1-Types

```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module foundation.1-types where

open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.identity-types using (Id)
open import foundation.levels using (Level; UU; lsuc)
open import foundation.sets using (UU-Set)
open import foundation.truncated-types using
  ( is-trunc; truncated-type-succ-Truncated-Type)
open import foundation.truncation-levels using (one-𝕋; zero-𝕋)
```

## 1-Types

```agda
is-1-type : {l : Level} → UU l → UU l
is-1-type = is-trunc one-𝕋

UU-1-Type : (l : Level) → UU (lsuc l)
UU-1-Type l = Σ (UU l) is-1-type

type-1-Type : {l : Level} → UU-1-Type l → UU l
type-1-Type = pr1

abstract
  is-1-type-type-1-Type :
    {l : Level} (A : UU-1-Type l) → is-1-type (type-1-Type A)
  is-1-type-type-1-Type = pr2

Id-Set : {l : Level} (X : UU-1-Type l) (x y : type-1-Type X) → UU-Set l
pr1 (Id-Set X x y) = Id x y
pr2 (Id-Set X x y) = is-1-type-type-1-Type X x y

1-type-Set :
  {l : Level} → UU-Set l → UU-1-Type l
1-type-Set A = truncated-type-succ-Truncated-Type zero-𝕋 A
```
