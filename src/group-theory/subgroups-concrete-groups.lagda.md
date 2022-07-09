---
title: Subgroups of concrete groups
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module group-theory.subgroups-concrete-groups where

open import foundation.dependent-pair-types
open import foundation.sets
open import foundation.universe-levels

open import group-theory.concrete-group-actions
open import group-theory.concrete-groups
open import group-theory.transitive-concrete-group-actions
```

## Idea

A subgroup of a concrete group `G` is a pointed transitive `G`-set.

## Definition

```agda
subgroup-action-Concrete-Group :
  {l1 : Level} (l2 : Level) (G : Concrete-Group l1) →
  classifying-type-Concrete-Group G → UU (l1 ⊔ lsuc l2)
subgroup-action-Concrete-Group l2 G u =
  Σ ( transitive-action-Concrete-Group l2 G)
    ( λ X → type-Set (action-transitive-action-Concrete-Group G X u))

subgroup-Concrete-Group :
  {l1 : Level} (l2 : Level) (G : Concrete-Group l1) → UU (l1 ⊔ lsuc l2)
subgroup-Concrete-Group l2 G =
  subgroup-action-Concrete-Group l2 G (shape-Concrete-Group G)
```
