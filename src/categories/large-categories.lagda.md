---
title: Formalisation of the Symmetry Book
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module categories.large-categories where

open import foundations public
open import Agda.Primitive public

record Large-Precat : Setω where
  constructor make-Large-Precat
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
    associative-comp-hom-Large-Precat :
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
associative-comp-hom-Large-Precat Set-Large-Precat X Y Z W h g f = refl
left-unit-law-comp-hom-Large-Precat Set-Large-Precat X Y f = refl
right-unit-law-comp-hom-Large-Precat Set-Large-Precat X Y f = refl
```

### Isomorphisms in large precategories

```agda

module _
  (C : Large-Precat) {l1 l2 : Level}
  (X : obj-Large-Precat C l1) (Y : obj-Large-Precat C l2)
  where

  type-hom-Large-Precat : UU (l1 ⊔ l2)
  type-hom-Large-Precat = type-Set (hom-Large-Precat C X Y)

  is-set-type-hom-Large-Precat : is-set type-hom-Large-Precat
  is-set-type-hom-Large-Precat = is-set-type-Set (hom-Large-Precat C X Y)

module _
  (C : Large-Precat) {l1 l2 l3 : Level}
  (X : obj-Large-Precat C l1) (Y : obj-Large-Precat C l2)
  (Z : obj-Large-Precat C l3)
  where

  ap-comp-hom-Large-Precat :
    {g g' : type-hom-Large-Precat C Y Z} (p : Id g g')
    {f f' : type-hom-Large-Precat C X Y} (q : Id f f') →
    Id ( comp-hom-Large-Precat C X Y Z g f)
       ( comp-hom-Large-Precat C X Y Z g' f')
  ap-comp-hom-Large-Precat p q = ap-binary (comp-hom-Large-Precat C X Y Z) p q

  comp-hom-Large-Precat' :
    type-hom-Large-Precat C X Y → type-hom-Large-Precat C Y Z →
    type-hom-Large-Precat C X Z
  comp-hom-Large-Precat' f g = comp-hom-Large-Precat C X Y Z g f

module _
  (C : Large-Precat) {l1 l2 : Level}
  (X : obj-Large-Precat C l1) (Y : obj-Large-Precat C l2)
  where
  
  is-iso-Large-Precat : type-hom-Large-Precat C X Y → UU (l1 ⊔ l2)
  is-iso-Large-Precat f =
    Σ ( type-hom-Large-Precat C Y X)
      ( λ g →
        ( Id (comp-hom-Large-Precat C Y X Y f g) (id-hom-Large-Precat C Y)) ×
        ( Id (comp-hom-Large-Precat C X Y X g f) (id-hom-Large-Precat C X)))

  all-elements-equal-is-iso-Large-Precat :
    (f : type-hom-Large-Precat C X Y)
    (H K : is-iso-Large-Precat f) → Id H K
  all-elements-equal-is-iso-Large-Precat f
    (pair g (pair p q)) (pair g' (pair p' q')) =
    eq-subtype
      ( λ g →
        is-prop-prod
          ( is-set-type-hom-Large-Precat C Y Y
            ( comp-hom-Large-Precat C Y X Y f g)
            ( id-hom-Large-Precat C Y))
          ( is-set-type-hom-Large-Precat C X X
            ( comp-hom-Large-Precat C X Y X g f)
            ( id-hom-Large-Precat C X)))
      ( ( inv (right-unit-law-comp-hom-Large-Precat C Y X g)) ∙
        ( ( ap ( comp-hom-Large-Precat C Y Y X g) (inv p')) ∙
          ( ( inv (associative-comp-hom-Large-Precat C Y X Y X g f g')) ∙
            ( ( ap ( comp-hom-Large-Precat' C Y X X g') q) ∙
              ( left-unit-law-comp-hom-Large-Precat C Y X g')))))

  is-prop-is-iso-Large-Precat :
    (f : type-hom-Large-Precat C X Y) → is-prop (is-iso-Large-Precat f)
  is-prop-is-iso-Large-Precat f =
    is-prop-all-elements-equal (all-elements-equal-is-iso-Large-Precat f)

  type-iso-Large-Precat : UU (l1 ⊔ l2)
  type-iso-Large-Precat = Σ (type-hom-Large-Precat C X Y) is-iso-Large-Precat

  is-set-type-iso-Large-Precat : is-set type-iso-Large-Precat
  is-set-type-iso-Large-Precat =
    is-set-subtype
      ( is-prop-is-iso-Large-Precat)
      ( is-set-type-hom-Large-Precat C X Y)

  iso-Large-Precat : UU-Set (l1 ⊔ l2)
  pr1 iso-Large-Precat = type-iso-Large-Precat
  pr2 iso-Large-Precat = is-set-type-iso-Large-Precat

```
