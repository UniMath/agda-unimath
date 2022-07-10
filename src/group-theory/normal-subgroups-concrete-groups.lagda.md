---
title: Normal subgroups of concrete groups
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module group-theory.normal-subgroups-concrete-groups where

open import foundation.universe-levels

open import group-theory.concrete-groups
open import group-theory.subgroups-concrete-groups
```

## Idea

A normal subgroup is a fixed point of the conjugation action on the (large) set of all subgroups

## Definition

```agda
normal-subgroup-Concrete-Group :
  {l1 : Level} (l2 : Level) (G : Concrete-Group l1) → UU (l1 ⊔ lsuc l2)
normal-subgroup-Concrete-Group l2 G =
  (u : classifying-type-Concrete-Group G) →
  subgroup-action-Concrete-Group l2 G u

module _
  {l1 l2 : Level} (G : Concrete-Group l1)
  (H : normal-subgroup-Concrete-Group l2 G)
  where

  subgroup-normal-subgroup-Concrete-Group : subgroup-Concrete-Group l2 G
  subgroup-normal-subgroup-Concrete-Group = H (shape-Concrete-Group G)
```
