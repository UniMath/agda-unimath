---
title: Higher group actions
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module group-theory.higher-group-actions where

open import foundation.universe-levels

open import group-theory.higher-groups
```

## Idea

An action of a higher group `G` on a type is just a type family over `BG`.

## Definition

```agda
action-∞-Group :
  {l1 : Level} (l2 : Level) (G : ∞-Group l1) → UU (l1 ⊔ lsuc l2)
action-∞-Group l2 G = classifying-type-∞-Group G → UU l2
```
