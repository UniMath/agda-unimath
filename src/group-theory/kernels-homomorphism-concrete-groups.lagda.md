---
title: Kernels of homomorphisms of concrete groups
---

```agda
module group-theory.kernels-homomorphism-concrete-groups where

open import foundation.universe-levels

open import group-theory.concrete-groups
open import group-theory.homomorphisms-concrete-groups
```

## Idea

The kernel of a concrete group homomorphsim `Bf : BG →* BH` is the connected component at the base point of the fiber of `Bf`.

## Definition

```agda
module _
  {l1 l2 : Level} (G : Concrete-Group l1) (H : Concrete-Group l2)
  (f : hom-Concrete-Groups G H)
  where
  
  concrete-group-kernel-hom-Concrete-Group : Concrete-Group (l1 ⊔ l2)
  concrete-group-kernel-hom-Concrete-Group = ?
  
```
