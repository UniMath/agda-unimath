# Full large subcategories

```agda
module category-theory.full-large-subcategories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.isomorphisms-in-large-categories
open import category-theory.large-categories

open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.subtypes
open import foundation.universe-levels
```

</details>

## Idea

A **full large subcategory** of a [large category](category-theory.large-categories.md) `C` consists of a [subtype](foundation.subtypes.md) of the type of objects of each universe level.

### Large subprecategories

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (γ : Level → Level)
  (C : Large-Category α β)
  where

  Full-Large-Subcategory : UUω
  Full-Large-Subcategory =
    {l : Level} → subtype (γ l) (obj-Large-Category C l)

module _
  {α : Level → Level} {β : Level → Level → Level} {γ : Level → Level}
  (C : Large-Category α β)
  (P : Full-Large-Subcategory γ C)
  where
    
  is-in-Full-Large-Subcategory :
    {l : Level} (X : obj-Large-Category C l) → UU (γ l)
  is-in-Full-Large-Subcategory X = is-in-subtype P X

  is-prop-is-in-Full-Large-Subcategory :
    {l : Level} (X : obj-Large-Category C l) →
    is-prop (is-in-Full-Large-Subcategory X)
  is-prop-is-in-Full-Large-Subcategory =
    is-prop-is-in-subtype P
                                                      
  obj-Full-Large-Subcategory : (l : Level) → UU (α l ⊔ γ l)
  obj-Full-Large-Subcategory l = type-subtype (P {l})

  hom-set-Full-Large-Subcategory :
    {l1 l2 : Level}
    (X : obj-Full-Large-Subcategory l1)
    (Y : obj-Full-Large-Subcategory l2) →
    Set (β l1 l2)
  hom-set-Full-Large-Subcategory X Y =
    hom-set-Large-Category C
      ( inclusion-subtype P X)
      ( inclusion-subtype P Y)

  hom-Full-Large-Subcategory :
    {l1 l2 : Level}
    (X : obj-Full-Large-Subcategory l1)
    (Y : obj-Full-Large-Subcategory l2) →
    UU (β l1 l2)
  hom-Full-Large-Subcategory X Y =
    hom-Large-Category C
      ( inclusion-subtype P X)
      ( inclusion-subtype P Y)
                            
  comp-hom-Full-Large-Subcategory :
    {l1 l2 l3 : Level}
    (X : obj-Full-Large-Subcategory l1)
    (Y : obj-Full-Large-Subcategory l2)
    (Z : obj-Full-Large-Subcategory l3) →
    hom-Full-Large-Subcategory Y Z → hom-Full-Large-Subcategory X Y →
    hom-Full-Large-Subcategory X Z
  comp-hom-Full-Large-Subcategory X Y Z =
    comp-hom-Large-Category C
                               
  id-hom-Full-Large-Subcategory :
    {l1 : Level} (X : obj-Full-Large-Subcategory l1) →
    hom-Full-Large-Subcategory X X
  id-hom-Full-Large-Subcategory X =
    id-hom-Large-Category C
                             
  associative-comp-hom-Full-Large-Subcategory :
    {l1 l2 l3 l4 : Level}
    (X : obj-Full-Large-Subcategory l1)
    (Y : obj-Full-Large-Subcategory l2)
    (Z : obj-Full-Large-Subcategory l3)
    (W : obj-Full-Large-Subcategory l4)
    (h : hom-Full-Large-Subcategory Z W)
    (g : hom-Full-Large-Subcategory Y Z)
    (f : hom-Full-Large-Subcategory X Y) →
    comp-hom-Full-Large-Subcategory X Y W
      ( comp-hom-Full-Large-Subcategory Y Z W h g)
      ( f) ＝
    comp-hom-Full-Large-Subcategory X Z W
      ( h)
      ( comp-hom-Full-Large-Subcategory X Y Z g f)
  associative-comp-hom-Full-Large-Subcategory X Y Z W =
    associative-comp-hom-Large-Category C
                                           
  left-unit-law-comp-hom-Full-Large-Subcategory :
    {l1 l2 : Level}
    (X : obj-Full-Large-Subcategory l1)
    (Y : obj-Full-Large-Subcategory l2)
    (f : hom-Full-Large-Subcategory X Y) →
    comp-hom-Full-Large-Subcategory X Y Y
      ( id-hom-Full-Large-Subcategory Y)
      ( f) ＝
    f
  left-unit-law-comp-hom-Full-Large-Subcategory X Y =
    left-unit-law-comp-hom-Large-Category C
                                             
  right-unit-law-comp-hom-Full-Large-Subcategory :
    {l1 l2 : Level}
    (X : obj-Full-Large-Subcategory l1)
    (Y : obj-Full-Large-Subcategory l2)
    (f : hom-Full-Large-Subcategory X Y) →
    comp-hom-Full-Large-Subcategory X X Y
      ( f)
      ( id-hom-Full-Large-Subcategory X) ＝
    f
  right-unit-law-comp-hom-Full-Large-Subcategory X Y =
    right-unit-law-comp-hom-Large-Category C

  large-precategory-Full-Large-Subcategory :
    Large-Category (λ l → α l ⊔ γ l) β
  large-precategory-Full-Large-Subcategory = ?

  iso-Full-Large-Subcategory :
    {l1 l2 : Level}
    (X : obj-Full-Large-Subcategory l1)
    (Y : obj-Full-Large-Subcategory l2) →
    UU (β l1 l1 ⊔ β l1 l2 ⊔ β l2 l1 ⊔ β l2 l2)
  iso-Full-Large-Subcategory X Y =
    iso-Large-Category C (inclusion-subtype P X) (inclusion-subtype P Y)

  iso-eq-Full-Large-Subcategory :
    {l1 : Level} (X Y : obj-Full-Large-Subcategory l1) →
    (X ＝ Y) → iso-Full-Large-Subcategory X Y
  iso-eq-Full-Large-Subcategory = ?
```

## Properties

### A large subprecategory of a large category is a large category

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} {γ : Level → Level}
  (C : Large-Category α β)
  (P : Full-Large-Subcategory γ C)
  where

  is-large-category-large-precategory-Full-Large-Category :
    is-large-category-Large-Category
      ( large-precategory-Full-Large-Subcategory C P)
  is-large-category-large-precategory-Full-Large-Category X =
    ?
```

