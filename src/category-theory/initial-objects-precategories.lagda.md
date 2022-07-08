---
title: Initial objects of a precategory
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module category-theory.initial-objects-precategories where

open import category-theory.precategories using
  ( Precat; obj-Precat; type-hom-Precat)
open import foundation.contractible-types using (is-contr)
open import foundation.dependent-pair-types using (Σ; pr1; pr2)
open import foundation-core.identity-types using (_＝_)
open import foundation.universe-levels using (UU; Level; _⊔_)
```

## Idea

The initial object of a precategory (if it exists) is an object with the universal property that there is a unique morphism from it to any object.

## Definition

```agda
initial-object : {l1 l2 : Level} (C : Precat l1 l2) → UU (l1 ⊔ l2)
initial-object C =
  Σ (obj-Precat C) λ i →
    (x : obj-Precat C) → is-contr (type-hom-Precat C i x)

module _ {l1 l2 : Level} (C : Precat l1 l2)
  (i : initial-object C) where

  object-initial-object : obj-Precat C
  object-initial-object = pr1 i

  morphism-initial-object :
    (x : obj-Precat C) →
    type-hom-Precat C object-initial-object x
  morphism-initial-object x = pr1 (pr2 i x)

  is-unique-morphism-initial-object :
    (x : obj-Precat C) (f : type-hom-Precat C object-initial-object x) →
    morphism-initial-object x ＝ f
  is-unique-morphism-initial-object x = pr2 (pr2 i x)
```
