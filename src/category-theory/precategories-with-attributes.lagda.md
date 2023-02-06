---
title: Precategories with attributes
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module category-theory.precategories-with-attributes where

open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.identity-types
open import foundation.sets
open import foundation.subtypes
open import foundation.universe-levels

open import category-theory.functors-precategories
open import category-theory.natural-transformations-precategories
open import category-theory.opposite-precategory
open import category-theory.precategories
open import category-theory.precategory-of-elements-of-a-presheaf
open import category-theory.pullbacks-precategories
```

## Idea

A category with attributes consists of:
* a category `C`, which we think of as a category of contexts and context morphisms
* a presheaf `Ty` on `C`, which we think of as giving the types in each context
* a functor `ext` from `∫ Ty` to `C`, which we think of as context extension
* a natural transformation `p` from `ext` to the projection from `∫ Ty` to `C`
such that
* the components of `p` are pullback squares

This is a reformulation of Definition 1, slide 24 of https://staff.math.su.se/palmgren/ErikP_Variants_CWF.pdf

```agda
record CwA {i j k} (C : Precat i j) : UU (i ⊔ j ⊔ lsuc k) where
  field
    Ty : functor-Precat (op C) (Set-Precat k)
    ext : functor-Precat (element-Precat C Ty) C
    p : nat-trans-Precat (element-Precat C Ty) C ext (proj₁-functor-element-Precat C Ty)
    is-pullback-p : (x y : obj-Precat (element-Precat C Ty)) (f : type-hom-Precat (element-Precat C Ty) x y) →
      is-pullback C _ _ _ _ _ _ _ _
        (squares-nat-trans-Precat (element-Precat C Ty) C ext (proj₁-functor-element-Precat C Ty) p f)
```
