---
title: Principal group actions
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module group-theory.principal-group-actions where

open import foundation.dependent-pair-types
open import foundation.equivalence-extensionality using (eq-htpy-equiv)
open import foundation.universe-levels

open import group-theory.group-actions using (Abstract-Group-Action)
open import group-theory.groups using
  ( Group; set-Group; equiv-mul-Group; associative-mul-Group)
```

## Idea

The principal group action is the action of a group on itself by multiplication from the left

## Definition

```agda
module _
  {l1 : Level} (G : Group l1)
  where
  
  principal-Abstract-Group-Action : Abstract-Group-Action G l1
  pr1 principal-Abstract-Group-Action = set-Group G
  pr1 (pr2 principal-Abstract-Group-Action) g = equiv-mul-Group G g
  pr2 (pr2 principal-Abstract-Group-Action) g h =
    eq-htpy-equiv (associative-mul-Group G g h)
```
