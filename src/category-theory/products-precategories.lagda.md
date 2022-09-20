---
title: Products in precategories
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module category-theory.products-precategories where

open import category-theory.precategories using
  ( Precat; obj-Precat; type-hom-Precat; comp-hom-Precat )
open import foundation.contractible-types using (is-contr)
open import foundation.dependent-pair-types using (Σ; pr1; pr2; _,_)
open import foundation.cartesian-product-types using (_×_)
open import foundation-core.identity-types using (_＝_; ap)
open import foundation.universe-levels using (UU; Level; _⊔_)
```

## Definition

```agda
product-span : {l1 l2 : Level} (C : Precat l1 l2) → obj-Precat C → obj-Precat C → UU (l1 ⊔ l2)
product-span C x y =
  -- Structure
  Σ (obj-Precat C) λ p →
  Σ (type-hom-Precat C p x) λ proj₁ →
  Σ (type-hom-Precat C p y) λ proj₂ →
  -- Universal property
    (z : obj-Precat C)
    (f : type-hom-Precat C z x) →
    (g : type-hom-Precat C z y) →
    is-contr (Σ (type-hom-Precat C z p) λ h →
      (comp-hom-Precat C proj₁ h ＝ f)
      × (comp-hom-Precat C proj₂ h ＝ g))

has-all-binary-products : {l1 l2 : Level} (C : Precat l1 l2) → UU (l1 ⊔ l2)
has-all-binary-products C = (x y : obj-Precat C) → product-span C x y


module _ {l1 l2 : Level} (C : Precat l1 l2)
  (t : has-all-binary-products C) where

  object-product-span : obj-Precat C → obj-Precat C → obj-Precat C
  object-product-span x y = pr1 (t x y)

  proj₁-product-span : (x y : obj-Precat C) → type-hom-Precat C (object-product-span x y) x
  proj₁-product-span x y = pr1 (pr2 (t x y))

  proj₂-product-span : (x y : obj-Precat C) → type-hom-Precat C (object-product-span x y) y
  proj₂-product-span x y = pr1 (pr2 (pr2 (t x y)))

  morphism-into-product-span :
    {x y z : obj-Precat C} →
    type-hom-Precat C z x →
    type-hom-Precat C z y →
    type-hom-Precat C z (object-product-span x y)
  morphism-into-product-span {x} {y} {z} f g = pr1 (pr1 (pr2 (pr2 (pr2 (t x y))) z f g))

  morphism-into-product-span-comm-proj₁ :
    {x y z : obj-Precat C} →
    (f : type-hom-Precat C z x) →
    (g : type-hom-Precat C z y) →
    comp-hom-Precat C (proj₁-product-span x y) (morphism-into-product-span f g) ＝ f
  morphism-into-product-span-comm-proj₁ {x} {y} {z} f g =
    pr1 (pr2 (pr1 (pr2 (pr2 (pr2 (t x y))) z f g)))

  morphism-into-product-span-comm-proj₂ :
    {x y z : obj-Precat C} →
    (f : type-hom-Precat C z x) →
    (g : type-hom-Precat C z y) →
    comp-hom-Precat C (proj₂-product-span x y) (morphism-into-product-span f g) ＝ g
  morphism-into-product-span-comm-proj₂ {x} {y} {z} f g =
    pr2 (pr2 (pr1 (pr2 (pr2 (pr2 (t x y))) z f g)))

  is-unique-morphism-product-span :
    {x y z : obj-Precat C} →
    (f : type-hom-Precat C z x) →
    (g : type-hom-Precat C z y) →
    (h : type-hom-Precat C z (object-product-span x y)) →
    comp-hom-Precat C (proj₁-product-span x y) h ＝ f →
    comp-hom-Precat C (proj₂-product-span x y) h ＝ g →
    morphism-into-product-span f g ＝ h
  is-unique-morphism-product-span {x} {y} {z} f g h comm1 comm2 =
    ap pr1 ((pr2 (pr2 (pr2 (pr2 (t x y))) z f g)) (h , (comm1 , comm2)))
```
