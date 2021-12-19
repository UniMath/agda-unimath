---
title: Formalisation of the Symmetry Book
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module categories.large-categories where

open import foundations public
open import Agda.Primitive public

record Large-Precat : Setω where
  field
    obj-Large-Precat :
      (l : Level) → UU (lsuc l)
    hom-Large-Precat :
      {l1 l2 : Level} → obj-Large-Precat l1 → obj-Large-Precat l2 →
      UU-Set (l1 ⊔ l2)
    comp-hom-Large-Precat :
      {l1 l2 l3 : Level} (X : obj-Large-Precat l1) (Y : obj-Large-Precat l2)
      (Z : obj-Large-Precat l3) →
      type-Set (hom-Large-Precat Y Z) → type-Set (hom-Large-Precat X Y) →
      type-Set (hom-Large-Precat X Z)
    id-hom-Large-Precat :
      {l1 : Level} (X : obj-Large-Precat l1) → type-Set (hom-Large-Precat X X)
    assocative-comp-hom-Large-Precat :
      {l1 l2 l3 l4 : Level} (X : obj-Large-Precat l1) (Y : obj-Large-Precat l2)
      (Z : obj-Large-Precat l3) (W : obj-Large-Precat l4) →
      (h : type-Set (hom-Large-Precat Z W))
      (g : type-Set (hom-Large-Precat Y Z))
      (f : type-Set (hom-Large-Precat X Y)) →
      Id ( comp-hom-Large-Precat X Y W (comp-hom-Large-Precat Y Z W h g) f)
         ( comp-hom-Large-Precat X Z W h (comp-hom-Large-Precat X Y Z g f))
    left-unit-law-comp-hom-Large-Precat :
      {l1 l2 : Level} (X : obj-Large-Precat l1) (Y : obj-Large-Precat l2)
      (f : type-Set (hom-Large-Precat X Y)) →
      Id ( comp-hom-Large-Precat X Y Y (id-hom-Large-Precat Y) f) f
    right-unit-law-comp-hom-Large-Precat :
      {l1 l2 : Level} (X : obj-Large-Precat l1) (Y : obj-Large-Precat l2)
      (f : type-Set (hom-Large-Precat X Y)) →
      Id ( comp-hom-Large-Precat X X Y f (id-hom-Large-Precat X)) f

open Large-Precat public

Set-Large-Precat : Large-Precat
obj-Large-Precat Set-Large-Precat = UU-Set
hom-Large-Precat Set-Large-Precat = hom-Set
comp-hom-Large-Precat Set-Large-Precat X Y Z g f = g ∘ f
id-hom-Large-Precat Set-Large-Precat X = id
assocative-comp-hom-Large-Precat Set-Large-Precat X Y Z W h g f = refl
left-unit-law-comp-hom-Large-Precat Set-Large-Precat X Y f = refl
right-unit-law-comp-hom-Large-Precat Set-Large-Precat X Y f = refl
```
