---
title: The precategory of semigroups
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module group-theory.precategory-of-semigroups where

open import category-theory.large-precategories using
  ( Large-Precat; obj-Large-Precat; hom-Large-Precat; comp-hom-Large-Precat;
    id-hom-Large-Precat; associative-comp-hom-Large-Precat;
    left-unit-law-comp-hom-Large-Precat; right-unit-law-comp-hom-Large-Precat)

open import foundation.universe-levels

open import group-theory.homomorphisms-semigroups using
  ( hom-Semigroup; comp-hom-Semigroup; id-hom-Semigroup;
    associative-comp-hom-Semigroup; left-unit-law-comp-hom-Semigroup;
    right-unit-law-comp-hom-Semigroup)
open import group-theory.semigroups using (Semigroup)
```

## Idea

Semigroups and semigroup homomorphisms form a precategory.

## Definition

### The precategory of semigroups

```agda
instance
  Semigroup-Large-Precat : Large-Precat lsuc (λ l1 l2 → l1 ⊔ l2)
  obj-Large-Precat Semigroup-Large-Precat = Semigroup
  hom-Large-Precat Semigroup-Large-Precat = hom-Semigroup
  comp-hom-Large-Precat Semigroup-Large-Precat {X = G} {H} {K} =
    comp-hom-Semigroup G H K
  id-hom-Large-Precat Semigroup-Large-Precat {X = G} =
    id-hom-Semigroup G
  associative-comp-hom-Large-Precat Semigroup-Large-Precat {X = G} {H} {K} {L} =
    associative-comp-hom-Semigroup G H K L
  left-unit-law-comp-hom-Large-Precat Semigroup-Large-Precat {X = G} {H} =
    left-unit-law-comp-hom-Semigroup G H
  right-unit-law-comp-hom-Large-Precat Semigroup-Large-Precat {X = G} {H} =
    right-unit-law-comp-hom-Semigroup G H
```
