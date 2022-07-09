---
title: The category of semigroups
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module group-theory.category-of-semigroups where

open import category-theory.large-categories using
  ( is-category-Large-Precat; Large-Cat; precat-Large-Cat;
    is-category-Large-Cat)

open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.equivalences using (_≃_; map-inv-is-equiv)
open import foundation.fundamental-theorem-of-identity-types using
  ( fundamental-theorem-id)
open import foundation.identity-types using (Id)
open import foundation.universe-levels using (Level; lsuc; _⊔_)

open import group-theory.isomorphisms-semigroups using
  ( id-iso-Semigroup; is-contr-total-iso-Semigroup; iso-eq-Semigroup;
    type-iso-Semigroup)
open import group-theory.precategory-of-semigroups using
  ( Semigroup-Large-Precat)
open import group-theory.semigroups using (Semigroup)
```

## Idea

Since isomorphic semigroups are equal, the precategory of semigroups is a category.

## Definition

```agda
is-category-Semigroup :
  is-category-Large-Precat Semigroup-Large-Precat
is-category-Semigroup G =
  fundamental-theorem-id G
    ( id-iso-Semigroup G)
    ( is-contr-total-iso-Semigroup G)
    ( iso-eq-Semigroup G)

extensionality-Semigroup :
  {l : Level} (G H : Semigroup l) → Id G H ≃ type-iso-Semigroup G H
pr1 (extensionality-Semigroup G H) = iso-eq-Semigroup G H
pr2 (extensionality-Semigroup G H) = is-category-Semigroup G H

eq-iso-Semigroup :
  {l : Level} (G H : Semigroup l) → type-iso-Semigroup G H → Id G H
eq-iso-Semigroup G H = map-inv-is-equiv (is-category-Semigroup G H)

Semigroup-Large-Cat : Large-Cat lsuc (λ l1 l2 → l1 ⊔ l2)
precat-Large-Cat Semigroup-Large-Cat = Semigroup-Large-Precat
is-category-Large-Cat Semigroup-Large-Cat = is-category-Semigroup
```
