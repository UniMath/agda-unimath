---
title: Formalisation of the Symmetry Book
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module categories.large-categories where

open import foundations.18-set-quotients public
open import Agda.Primitive public

record Large-Precat (α : Level → Level) (β : Level → Level → Level) : Setω where
  constructor make-Large-Precat
  field
    obj-Large-Precat :
      (l : Level) → UU (α l)
    hom-Large-Precat :
      {l1 l2 : Level} → obj-Large-Precat l1 → obj-Large-Precat l2 →
      UU-Set (β l1 l2)
    comp-hom-Large-Precat :
      {l1 l2 l3 : Level} {X : obj-Large-Precat l1} {Y : obj-Large-Precat l2}
      {Z : obj-Large-Precat l3} →
      type-Set (hom-Large-Precat Y Z) → type-Set (hom-Large-Precat X Y) →
      type-Set (hom-Large-Precat X Z)
    id-hom-Large-Precat :
      {l1 : Level} {X : obj-Large-Precat l1} → type-Set (hom-Large-Precat X X)
    associative-comp-hom-Large-Precat :
      {l1 l2 l3 l4 : Level} {X : obj-Large-Precat l1} {Y : obj-Large-Precat l2}
      {Z : obj-Large-Precat l3} {W : obj-Large-Precat l4} →
      (h : type-Set (hom-Large-Precat Z W))
      (g : type-Set (hom-Large-Precat Y Z))
      (f : type-Set (hom-Large-Precat X Y)) →
      Id ( comp-hom-Large-Precat (comp-hom-Large-Precat h g) f)
         ( comp-hom-Large-Precat h (comp-hom-Large-Precat g f))
    left-unit-law-comp-hom-Large-Precat :
      {l1 l2 : Level} {X : obj-Large-Precat l1} {Y : obj-Large-Precat l2}
      (f : type-Set (hom-Large-Precat X Y)) →
      Id ( comp-hom-Large-Precat id-hom-Large-Precat f) f
    right-unit-law-comp-hom-Large-Precat :
      {l1 l2 : Level} {X : obj-Large-Precat l1} {Y : obj-Large-Precat l2}
      (f : type-Set (hom-Large-Precat X Y)) →
      Id ( comp-hom-Large-Precat f id-hom-Large-Precat) f

open Large-Precat public

Set-Large-Precat : Large-Precat lsuc (λ l1 l2 → l1 ⊔ l2)
obj-Large-Precat Set-Large-Precat = UU-Set
hom-Large-Precat Set-Large-Precat = hom-Set
comp-hom-Large-Precat Set-Large-Precat g f = g ∘ f
id-hom-Large-Precat Set-Large-Precat = id
associative-comp-hom-Large-Precat Set-Large-Precat h g f = refl
left-unit-law-comp-hom-Large-Precat Set-Large-Precat f = refl
right-unit-law-comp-hom-Large-Precat Set-Large-Precat f = refl
```

### Isomorphisms in large precategories

```agda

module _
  {α : Level → Level} {β : Level → Level → Level}
  (C : Large-Precat α β) {l1 l2 : Level}
  (X : obj-Large-Precat C l1) (Y : obj-Large-Precat C l2)
  where

  type-hom-Large-Precat : UU (β l1 l2)
  type-hom-Large-Precat = type-Set (hom-Large-Precat C X Y)

  is-set-type-hom-Large-Precat : is-set type-hom-Large-Precat
  is-set-type-hom-Large-Precat = is-set-type-Set (hom-Large-Precat C X Y)

module _
  {α : Level → Level} {β : Level → Level → Level}
  (C : Large-Precat α β) {l1 l2 l3 : Level}
  {X : obj-Large-Precat C l1} {Y : obj-Large-Precat C l2}
  {Z : obj-Large-Precat C l3}
  where

  ap-comp-hom-Large-Precat :
    {g g' : type-hom-Large-Precat C Y Z} (p : Id g g')
    {f f' : type-hom-Large-Precat C X Y} (q : Id f f') →
    Id ( comp-hom-Large-Precat C g f)
       ( comp-hom-Large-Precat C g' f')
  ap-comp-hom-Large-Precat p q = ap-binary (comp-hom-Large-Precat C) p q

  comp-hom-Large-Precat' :
    type-hom-Large-Precat C X Y → type-hom-Large-Precat C Y Z →
    type-hom-Large-Precat C X Z
  comp-hom-Large-Precat' f g = comp-hom-Large-Precat C g f

module _
  {α : Level → Level} {β : Level → Level → Level}
  (C : Large-Precat α β) {l1 l2 : Level}
  (X : obj-Large-Precat C l1) (Y : obj-Large-Precat C l2)
  where
  
  is-iso-hom-Large-Precat :
    type-hom-Large-Precat C X Y → UU (β l1 l1 ⊔ β l2 l1 ⊔ β l2 l2)
  is-iso-hom-Large-Precat f =
    Σ ( type-hom-Large-Precat C Y X)
      ( λ g →
        ( Id (comp-hom-Large-Precat C f g) (id-hom-Large-Precat C)) ×
        ( Id (comp-hom-Large-Precat C g f) (id-hom-Large-Precat C)))

  all-elements-equal-is-iso-hom-Large-Precat :
    (f : type-hom-Large-Precat C X Y)
    (H K : is-iso-hom-Large-Precat f) → Id H K
  all-elements-equal-is-iso-hom-Large-Precat f
    (pair g (pair p q)) (pair g' (pair p' q')) =
    eq-subtype
      ( λ g →
        is-prop-prod
          ( is-set-type-hom-Large-Precat C Y Y
            ( comp-hom-Large-Precat C f g)
            ( id-hom-Large-Precat C))
          ( is-set-type-hom-Large-Precat C X X
            ( comp-hom-Large-Precat C g f)
            ( id-hom-Large-Precat C)))
      ( ( inv (right-unit-law-comp-hom-Large-Precat C g)) ∙
        ( ( ap ( comp-hom-Large-Precat C g) (inv p')) ∙
          ( ( inv (associative-comp-hom-Large-Precat C g f g')) ∙
            ( ( ap ( comp-hom-Large-Precat' C g') q) ∙
              ( left-unit-law-comp-hom-Large-Precat C g')))))

  is-prop-is-iso-hom-Large-Precat :
    (f : type-hom-Large-Precat C X Y) → is-prop (is-iso-hom-Large-Precat f)
  is-prop-is-iso-hom-Large-Precat f =
    is-prop-all-elements-equal (all-elements-equal-is-iso-hom-Large-Precat f)

  type-iso-Large-Precat : UU (β l1 l1 ⊔ β l1 l2 ⊔ β l2 l1 ⊔ β l2 l2)
  type-iso-Large-Precat =
    Σ (type-hom-Large-Precat C X Y) is-iso-hom-Large-Precat

  is-set-type-iso-Large-Precat : is-set type-iso-Large-Precat
  is-set-type-iso-Large-Precat =
    is-set-subtype
      ( is-prop-is-iso-hom-Large-Precat)
      ( is-set-type-hom-Large-Precat C X Y)

  iso-Large-Precat : UU-Set (β l1 l1 ⊔ β l1 l2 ⊔ β l2 l1 ⊔ β l2 l2)
  pr1 iso-Large-Precat = type-iso-Large-Precat
  pr2 iso-Large-Precat = is-set-type-iso-Large-Precat

  hom-iso-Large-Precat : type-iso-Large-Precat → type-hom-Large-Precat C X Y
  hom-iso-Large-Precat = pr1

  is-iso-hom-iso-Large-Precat :
    (f : type-iso-Large-Precat) →
    is-iso-hom-Large-Precat (hom-iso-Large-Precat f)
  is-iso-hom-iso-Large-Precat f = pr2 f

  hom-inv-iso-Large-Precat : type-iso-Large-Precat → type-hom-Large-Precat C Y X
  hom-inv-iso-Large-Precat f = pr1 (pr2 f)

  issec-hom-inv-iso-Large-Precat :
    (f : type-iso-Large-Precat) →
    Id ( comp-hom-Large-Precat C
         ( hom-iso-Large-Precat f)
         ( hom-inv-iso-Large-Precat f))
       ( id-hom-Large-Precat C)
  issec-hom-inv-iso-Large-Precat f = pr1 (pr2 (pr2 f))

  isretr-hom-inv-iso-Large-Precat :
    (f : type-iso-Large-Precat) →
    Id ( comp-hom-Large-Precat C
         ( hom-inv-iso-Large-Precat f)
         ( hom-iso-Large-Precat f))
       ( id-hom-Large-Precat C)
  isretr-hom-inv-iso-Large-Precat f = pr2 (pr2 (pr2 f))

module _
  {α : Level → Level} {β : Level → Level → Level}
  (C : Large-Precat α β) {l1 : Level} (X : obj-Large-Precat C l1)
  where

  id-iso-Large-Precat : type-iso-Large-Precat C X X
  pr1 id-iso-Large-Precat = id-hom-Large-Precat C
  pr1 (pr2 id-iso-Large-Precat) = id-hom-Large-Precat C
  pr1 (pr2 (pr2 id-iso-Large-Precat)) =
    left-unit-law-comp-hom-Large-Precat C (id-hom-Large-Precat C)
  pr2 (pr2 (pr2 id-iso-Large-Precat)) =
    left-unit-law-comp-hom-Large-Precat C (id-hom-Large-Precat C)

  iso-eq-Large-Precat :
    (Y : obj-Large-Precat C l1) → Id X Y → type-iso-Large-Precat C X Y
  iso-eq-Large-Precat .X refl = id-iso-Large-Precat

module _
  {α : Level → Level} {β : Level → Level → Level}
  (C : Large-Precat α β)
  where
  
  is-category-Large-Precat : Setω
  is-category-Large-Precat =
    {l : Level} (X Y : obj-Large-Precat C l) →
    is-equiv (iso-eq-Large-Precat C X Y)

record Large-Cat (α : Level → Level) (β : Level → Level → Level) : Setω where
  constructor make-Large-Cat
  field
    precat-Large-Cat : Large-Precat α β
    is-category-Large-Cat : is-category-Large-Precat precat-Large-Cat

open Large-Cat public

```
