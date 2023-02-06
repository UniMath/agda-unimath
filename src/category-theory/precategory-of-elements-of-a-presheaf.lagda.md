---
title: Precategory of elements
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module category-theory.precategory-of-elements-of-a-presheaf where

open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.identity-types
open import foundation.sets
open import foundation.subtypes
open import foundation.universe-levels

open import category-theory.functors-precategories
open import category-theory.opposite-precategory
open import category-theory.precategories
```

## Idea

Let `F : C^op → Set` be a presheaf on a precategory `C`. The category of elements of `F` consists of:
* objects are pairs `(A , a)` where `A` is an object in `C` and `a : F(A)`
* a morphism from `(A , a)` to `(B , b)` is a morphism `f : hom_C(A, B)` such that `a = F(f)(b)`

```agda
module _ {i j k} (C : Precat i j) (F : functor-Precat (op C) (Set-Precat k)) where

  element-Precat : Precat (i ⊔ k) (j ⊔ k)
  pr1 element-Precat =
    Σ (obj-Precat C) λ A → pr1 (obj-functor-Precat (op C) (Set-Precat k) F A)
  pr1 (pr2 element-Precat) (A , a) (B , b) =
    set-subset (hom-Precat C A B) λ f →
               Id-Prop (obj-functor-Precat (op C) (Set-Precat k) F A)
                 a
                 (hom-functor-Precat (op C) (Set-Precat k) F f b)
  pr1 (pr1 (pr1 (pr2 (pr2 element-Precat))) (f , p) (g , q)) =
    comp-hom-Precat C f g
  pr2 (pr1 (pr1 (pr2 (pr2 element-Precat))) (f , p) (g , q)) =
    q ∙
    (ap (hom-functor-Precat (op C) (Set-Precat k) F g) p ∙
    htpy-eq (inv (respects-comp-functor-Precat (op C) (Set-Precat k) F g f)) _)
  pr2 (pr1 (pr2 (pr2 element-Precat))) h g f =
    eq-type-subtype
      (λ f → Id-Prop (obj-functor-Precat (op C) (Set-Precat k) F _)
                 _
                 (hom-functor-Precat (op C) (Set-Precat k) F f _))
      (assoc-comp-hom-Precat C (pr1 h) (pr1 g) (pr1 f))
  pr1 (pr1 (pr2 (pr2 (pr2 element-Precat))) x) =
    id-hom-Precat C
  pr2 (pr1 (pr2 (pr2 (pr2 element-Precat))) x) =
    inv (htpy-eq (respects-id-functor-Precat (op C) (Set-Precat k) F (pr1 x)) (pr2 x))
  pr1 (pr2 (pr2 (pr2 (pr2 element-Precat)))) f =
    eq-type-subtype
      (λ f → Id-Prop (obj-functor-Precat (op C) (Set-Precat k) F _)
                 _
                 (hom-functor-Precat (op C) (Set-Precat k) F f _))
      (left-unit-law-comp-hom-Precat C (pr1 f))
  pr2 (pr2 (pr2 (pr2 (pr2 element-Precat)))) f =
    eq-type-subtype
      (λ f → Id-Prop (obj-functor-Precat (op C) (Set-Precat k) F _)
               _
               (hom-functor-Precat (op C) (Set-Precat k) F f _))
      (right-unit-law-comp-hom-Precat C (pr1 f))
```

### Projection to C is a functor

```agda
module _ {i j k} (C : Precat i j) (F : functor-Precat (op C) (Set-Precat k)) where

  proj₁-functor-element-Precat : functor-Precat (element-Precat C F) C
  pr1 proj₁-functor-element-Precat = pr1
  pr1 (pr2 proj₁-functor-element-Precat) f = pr1 f
  pr1 (pr2 (pr2 proj₁-functor-element-Precat)) g f = refl
  pr2 (pr2 (pr2 proj₁-functor-element-Precat)) x = refl
```
