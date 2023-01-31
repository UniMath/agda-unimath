---
title: The category of groups
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module group-theory.category-of-groups where

open import category-theory.large-categories using
  ( is-category-Large-Precat; Large-Cat; precat-Large-Cat;
    is-category-Large-Cat)

open import foundation.equivalences
open import foundation.fundamental-theorem-of-identity-types
open import foundation.identity-types
open import foundation.universe-levels

open import group-theory.groups
open import group-theory.isomorphisms-groups
open import group-theory.precategory-of-groups using (Group-Large-Precat)
```

## Definition

```agda
is-category-Group : is-category-Large-Precat Group-Large-Precat
is-category-Group G =
  fundamental-theorem-id
    ( is-contr-total-iso-Group G)
    ( iso-eq-Group G)

eq-iso-Group : {l : Level} (G H : Group l) → type-iso-Group G H → Id G H
eq-iso-Group G H = map-inv-is-equiv (is-category-Group G H)

Group-Large-Cat : Large-Cat lsuc (λ l1 l2 → l1 ⊔ l2)
precat-Large-Cat Group-Large-Cat = Group-Large-Precat
is-category-Large-Cat Group-Large-Cat = is-category-Group
```
