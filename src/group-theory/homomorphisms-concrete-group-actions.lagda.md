---
title: Morphisms of concrete group actions
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module group-theory.homomorphisms-concrete-group-actions where

open import foundation.sets
open import foundation.universe-levels

open import group-theory.concrete-group-actions
open import group-theory.concrete-groups
```

## Definition

### Morphisms of concrete group actions

```agda
module _
  {l1 : Level} (G : Concrete-Group l1)
  where

  hom-action-Concrete-Group :
    {l2 l3 : Level} →
    action-Concrete-Group l2 G → action-Concrete-Group l3 G → UU (l1 ⊔ l2 ⊔ l3)
  hom-action-Concrete-Group X Y =
    (x : classifying-type-Concrete-Group G) → type-Set (X x) → type-Set (Y x)
```
