---
title: Products in precategories
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module category-theory.exponential-objects-precategories where

open import category-theory.precategories using
  ( Precat; obj-Precat; type-hom-Precat; comp-hom-Precat;
    id-hom-Precat)
open import category-theory.products-precategories using
  ( has-all-binary-products; object-product-span;
    product-of-morphisms)
open import foundation.dependent-pair-types using (Σ; pr1; pr2; _,_)
-- open import foundation.cartesian-product-types using (_×_)
open import foundation-core.identity-types using (_＝_; ap)
open import foundation.unique-existence using (∃!)
open import foundation.universe-levels using (UU; Level; _⊔_)
```

## Idea

Let `C` be a category with all binary products. For objects `x` and `y` in `C`, an exponential (often denoted y^x) consists of:
- an object `e`
- a morphism `ev : hom (e × x) y`
such that for every object `z` and morphism `f : hom (z × x) y` there exists a unique morphism `g : hom z e` such that
- `comp (g × id x) ev = f`.

We say that `C` has all exponentials if there is a choice of an exponential for each pair of objects.

## Definition

```agda
module _ {l1 l2 : Level} (C : Precat l1 l2) (p : has-all-binary-products C) where

  exponential : obj-Precat C → obj-Precat C → UU (l1 ⊔ l2)
  exponential x y =
    Σ (obj-Precat C) (λ e →
    Σ (type-hom-Precat C (object-product-span C p e x) y) λ ev →
      (z : obj-Precat C) (f : type-hom-Precat C (object-product-span C p z x) y) →
        ∃! (type-hom-Precat C z e) λ g →
           comp-hom-Precat C ev (product-of-morphisms C p g (id-hom-Precat C)) ＝ f)

  has-all-exponentials : UU (l1 ⊔ l2)
  has-all-exponentials = (x y : obj-Precat C) → exponential x y

module _ {l1 l2 : Level} (C : Precat l1 l2)
  (p : has-all-binary-products C)
  (t : has-all-exponentials C p)
  (x y : obj-Precat C) where

  object-exponential : obj-Precat C
  object-exponential = pr1 (t x y)

  eval-exponential : type-hom-Precat C (object-product-span C p object-exponential x) y
  eval-exponential = pr1 (pr2 (t x y))

  morphism-into-exponential :
    {z : obj-Precat C} →
    type-hom-Precat C (object-product-span C p z x) y →
    type-hom-Precat C z object-exponential
  morphism-into-exponential {z} f = pr1 (pr1 (pr2 (pr2 (t x y)) z f))

  morphism-into-exponential-comm :
    {z : obj-Precat C} →
    (f : type-hom-Precat C (object-product-span C p z x) y)
    → comp-hom-Precat C
        eval-exponential
        (product-of-morphisms C p
          (morphism-into-exponential f)
          (id-hom-Precat C))
    ＝ f
  morphism-into-exponential-comm {z} f = pr2 (pr1 (pr2 (pr2 (t x y)) z f))

  is-unique-morphism-into-exponential :
    {z : obj-Precat C} →
    (f : type-hom-Precat C (object-product-span C p z x) y)
    (g : type-hom-Precat C z object-exponential)
    → comp-hom-Precat C
        eval-exponential
        (product-of-morphisms C p g (id-hom-Precat C))
      ＝ f
    → morphism-into-exponential f ＝ g
  is-unique-morphism-into-exponential {z} f g q =
    ap pr1 (pr2 (pr2 (pr2 (t x y)) z f) (g , q))
```
