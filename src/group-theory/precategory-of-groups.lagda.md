---
title: The precategory of groups
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module group-theory.precategory-of-groups where

open import category-theory.large-precategories using
  ( Large-Precat; obj-Large-Precat; hom-Large-Precat; comp-hom-Large-Precat;
    id-hom-Large-Precat; associative-comp-hom-Large-Precat;
    left-unit-law-comp-hom-Large-Precat; right-unit-law-comp-hom-Large-Precat)

open import foundation.universe-levels

open import group-theory.groups
open import group-theory.homomorphisms-groups using
  ( hom-Group; comp-hom-Group; id-hom-Group; associative-comp-hom-Group;
    left-unit-law-comp-hom-Group; right-unit-law-comp-hom-Group)
```

## Definition

```agda
instance
  Group-Large-Precat : Large-Precat lsuc (λ l1 l2 → l1 ⊔ l2)
  obj-Large-Precat Group-Large-Precat = Group
  hom-Large-Precat Group-Large-Precat = hom-Group
  comp-hom-Large-Precat Group-Large-Precat {X = G} {H} {K} =
    comp-hom-Group G H K
  id-hom-Large-Precat Group-Large-Precat {X = G} =
    id-hom-Group G
  associative-comp-hom-Large-Precat Group-Large-Precat {X = G} {H} {K} {L} =
    associative-comp-hom-Group G H K L
  left-unit-law-comp-hom-Large-Precat Group-Large-Precat {X = G} {H} =
    left-unit-law-comp-hom-Group G H
  right-unit-law-comp-hom-Large-Precat Group-Large-Precat {X = G} {H} =
    right-unit-law-comp-hom-Group G H
```
