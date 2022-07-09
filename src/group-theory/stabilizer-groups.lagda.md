---
title: Stabilizer groups
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module group-theory.stabilizer-groups where

open import foundation.dependent-pair-types using (Σ)
open import foundation.identity-types using (Id)
open import foundation.universe-levels using (Level; UU; _⊔_)

open import group-theory.group-actions using
  ( Abstract-Group-Action; type-Abstract-Group-Action;
    mul-Abstract-Group-Action)
open import group-theory.groups using (Group; type-Group)
```

## Idea

Given a G-set `X`, the stabilizer group at an element `x` of `X` is the subgroup of elements `g` of `G` that keep `x` fixed.

## Definition

```agda
module _
  {l1 l2 : Level} (G : Group l1) (X : Abstract-Group-Action G l2)
  where

  type-stabilizer-Abstract-Group-Action :
    type-Abstract-Group-Action G X → UU (l1 ⊔ l2)
  type-stabilizer-Abstract-Group-Action x =
    Σ (type-Group G) (λ g → Id (mul-Abstract-Group-Action G X g x) x)
```

