---
title: Products in precategories
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module category-theory.products-precategories where

open import category-theory.precategories using
  ( Precat; obj-Precat; type-hom-Precat; comp-hom-Precat )
open import foundation.dependent-pair-types using (Σ; pr1; pr2; _,_)
open import foundation.cartesian-product-types using (_×_)
open import foundation-core.identity-types using (_＝_; ap)
open import foundation.unique-existence using (∃!)
open import foundation.universe-levels using (UU; Level; _⊔_)
```

## Idea

A product of two objects `x` and `x` in a category `C` consists of:
- an object `p`
- morphisms `proj₁ : hom p x` and `proj₂ : hom p y`
such that for every object `z` and morphisms `f : hom z x` and `g : hom z y` there exists a unique morphism `h : hom z p` such that
- `comp proj₁ h = f`
- `comp proj₂ h = g`.

We say that `C` has all binary products if there is a choice of a product for each pair of objects in `C`.

## Definition

```agda
module _ {l1 l2 : Level} (C : Precat l1 l2) where

  is-product :
    (x y p : obj-Precat C) →
    type-hom-Precat C p x →
    type-hom-Precat C p y →
    UU (l1 ⊔ l2)
  is-product x y p proj₁ proj₂ =
    (z : obj-Precat C)
    (f : type-hom-Precat C z x) →
    (g : type-hom-Precat C z y) →
    (∃! (type-hom-Precat C z p) λ h →
        (comp-hom-Precat C proj₁ h ＝ f)
        × (comp-hom-Precat C proj₂ h ＝ g))

  product-span : obj-Precat C → obj-Precat C → UU (l1 ⊔ l2)
  product-span x y =
    Σ (obj-Precat C) λ p →
    Σ (type-hom-Precat C p x) λ proj₁ →
    Σ (type-hom-Precat C p y) λ proj₂ →
      is-product x y p proj₁ proj₂

  has-all-binary-products : UU (l1 ⊔ l2)
  has-all-binary-products = (x y : obj-Precat C) → product-span x y


module _ {l1 l2 : Level} (C : Precat l1 l2)
  (t : has-all-binary-products C) where

  object-product-span : obj-Precat C → obj-Precat C → obj-Precat C
  object-product-span x y = pr1 (t x y)

  proj₁-product-span : (x y : obj-Precat C) → type-hom-Precat C (object-product-span x y) x
  proj₁-product-span x y = pr1 (pr2 (t x y))

  proj₂-product-span : (x y : obj-Precat C) → type-hom-Precat C (object-product-span x y) y
  proj₂-product-span x y = pr1 (pr2 (pr2 (t x y)))

  module _ (x y z : obj-Precat C)
    (f : type-hom-Precat C z x)
    (g : type-hom-Precat C z y) where

    morphism-into-product-span : type-hom-Precat C z (object-product-span x y)
    morphism-into-product-span = pr1 (pr1 (pr2 (pr2 (pr2 (t x y))) z f g))

    morphism-into-product-span-comm-proj₁ :
      comp-hom-Precat C (proj₁-product-span x y) morphism-into-product-span ＝ f
    morphism-into-product-span-comm-proj₁ =
      pr1 (pr2 (pr1 (pr2 (pr2 (pr2 (t x y))) z f g)))

    morphism-into-product-span-comm-proj₂ :
      comp-hom-Precat C (proj₂-product-span x y) morphism-into-product-span ＝ g
    morphism-into-product-span-comm-proj₂ =
      pr2 (pr2 (pr1 (pr2 (pr2 (pr2 (t x y))) z f g)))

    is-unique-morphism-into-product-span :
      (h : type-hom-Precat C z (object-product-span x y)) →
      comp-hom-Precat C (proj₁-product-span x y) h ＝ f →
      comp-hom-Precat C (proj₂-product-span x y) h ＝ g →
      morphism-into-product-span ＝ h
    is-unique-morphism-into-product-span h comm1 comm2 =
      ap pr1 ((pr2 (pr2 (pr2 (pr2 (t x y))) z f g)) (h , (comm1 , comm2)))
```

## Properties

### Products of morphisms

If `C` has all binary products then for any pair of morphisms `f : hom x₁ y₁` and `g : hom x₂ y₂` we can construct a morphism `f × g : hom (x₁ × x₂) (y₁ × y₂)`.

```agda
module _ {l1 l2 : Level} (C : Precat l1 l2)
  (t : has-all-binary-products C)
  {x₁ x₂ y₁ y₂ : obj-Precat C}
  (f : type-hom-Precat C x₁ y₁)
  (g : type-hom-Precat C x₂ y₂) where

  product-of-morphisms :
    type-hom-Precat C
      (object-product-span C t x₁ x₂)
      (object-product-span C t y₁ y₂)
  product-of-morphisms =
    morphism-into-product-span C t _ _ _
      (comp-hom-Precat C f (proj₁-product-span C t x₁ x₂))
      (comp-hom-Precat C g (proj₂-product-span C t x₁ x₂))
```
