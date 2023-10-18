# Subcategories

```agda
module category-theory.subcategories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.categories
open import category-theory.embeddings-precategories
open import category-theory.faithful-functors-precategories
open import category-theory.functors-categories
open import category-theory.functors-precategories
open import category-theory.maps-categories
open import category-theory.maps-precategories
open import category-theory.precategories
open import category-theory.subprecategories

open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.subtypes
open import foundation.universe-levels
```

</details>

## Idea

A **subcategory** of a [category](category-theory.categories.md) `C` consists of
a [subtype](foundation-core.subtypes.md) `P₀` of the objects of `C`, and a
family of subtypes `P₁`

```text
  P₁ : (X Y : obj C) → P₀ X → P₀ Y → subtype (hom X Y)
```

of the morphisms of `C`, such that `P₁` contains all identity morphisms of
objects in `P₀` and is closed under composition.

## Definitions

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Category l1 l2)
  (P₀ : subtype l3 (obj-Category C))
  (P₁ : (x y : obj-Category C) → subtype l4 (hom-Category C x y))
  where

  contains-id-subtype-Category : UU (l1 ⊔ l3 ⊔ l4)
  contains-id-subtype-Category =
    contains-id-subtype-Precategory (precategory-Category C) P₀ P₁

  is-prop-contains-id-subtype-Category :
    is-prop contains-id-subtype-Category
  is-prop-contains-id-subtype-Category =
    is-prop-contains-id-subtype-Precategory (precategory-Category C) P₀ P₁

  contains-id-prop-subtype-Category : Prop (l1 ⊔ l3 ⊔ l4)
  contains-id-prop-subtype-Category =
    contains-id-prop-subtype-Precategory (precategory-Category C) P₀ P₁

  is-closed-under-composition-subtype-Category : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  is-closed-under-composition-subtype-Category =
    is-closed-under-composition-subtype-Precategory
      ( precategory-Category C) P₀ P₁

  is-prop-is-closed-under-composition-subtype-Category :
    is-prop is-closed-under-composition-subtype-Category
  is-prop-is-closed-under-composition-subtype-Category =
    is-prop-is-closed-under-composition-subtype-Precategory
      ( precategory-Category C) P₀ P₁

  is-closed-under-composition-prop-subtype-Category : Prop (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  is-closed-under-composition-prop-subtype-Category =
    is-closed-under-composition-prop-subtype-Precategory
      ( precategory-Category C) P₀ P₁
```

### The predicate of being a subcategory

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Category l1 l2)
  (P₀ : subtype l3 (obj-Category C))
  (P₁ : (x y : obj-Category C) → subtype l4 (hom-Category C x y))
  where

  is-subcategory-Prop : Prop (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  is-subcategory-Prop =
    is-subprecategory-Prop (precategory-Category C) P₀ P₁

  is-subcategory : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  is-subcategory = type-Prop is-subcategory-Prop

  is-prop-is-subcategory : is-prop (is-subcategory)
  is-prop-is-subcategory = is-prop-type-Prop is-subcategory-Prop

  contains-id-is-subcategory :
    is-subcategory → contains-id-subtype-Category C P₀ P₁
  contains-id-is-subcategory = pr1

  is-closed-under-composition-is-subcategory :
    is-subcategory → is-closed-under-composition-subtype-Category C P₀ P₁
  is-closed-under-composition-is-subcategory = pr2
```

### Subcategories

```agda
Subcategory :
  {l1 l2 : Level} (l3 l4 : Level)
  (C : Category l1 l2) →
  UU (l1 ⊔ l2 ⊔ lsuc l3 ⊔ lsuc l4)
Subcategory l3 l4 C = Subprecategory l3 l4 (precategory-Category C)

module _
  {l1 l2 l3 l4 : Level}
  (C : Category l1 l2)
  (P : Subcategory l3 l4 C)
  where

  subtype-obj-Subcategory : subtype l3 (obj-Category C)
  subtype-obj-Subcategory = pr1 P

  obj-Subcategory : UU (l1 ⊔ l3)
  obj-Subcategory = type-subtype subtype-obj-Subcategory

  inclusion-obj-Subcategory : obj-Subcategory → obj-Category C
  inclusion-obj-Subcategory = inclusion-subtype subtype-obj-Subcategory

  is-in-obj-Subcategory : (x : obj-Category C) → UU l3
  is-in-obj-Subcategory = is-in-subtype subtype-obj-Subcategory

  is-in-obj-inclusion-obj-Subcategory :
    (x : obj-Subcategory) →
    is-in-obj-Subcategory (inclusion-obj-Subcategory x)
  is-in-obj-inclusion-obj-Subcategory =
    is-in-subtype-inclusion-subtype subtype-obj-Subcategory

  subtype-hom-Subcategory :
    (x y : obj-Category C) → subtype l4 (hom-Category C x y)
  subtype-hom-Subcategory = pr1 (pr2 P)

  hom-Subcategory : (x y : obj-Subcategory) → UU (l2 ⊔ l4)
  hom-Subcategory = hom-Subprecategory (precategory-Category C) P

  inclusion-hom-Subcategory :
    (x y : obj-Subcategory) →
    hom-Subcategory x y →
    hom-Category C
      ( inclusion-obj-Subcategory x)
      ( inclusion-obj-Subcategory y)
  inclusion-hom-Subcategory =
    inclusion-hom-Subprecategory (precategory-Category C) P

  is-in-hom-Subcategory :
    (x y : obj-Category C) (f : hom-Category C x y) → UU l4
  is-in-hom-Subcategory x y = is-in-subtype (subtype-hom-Subcategory x y)

  is-in-hom-inclusion-hom-Subcategory :
    (x y : obj-Subcategory) (f : hom-Subcategory x y) →
    is-in-hom-Subcategory
      ( inclusion-obj-Subcategory x)
      ( inclusion-obj-Subcategory y)
      ( inclusion-hom-Subcategory x y f)
  is-in-hom-inclusion-hom-Subcategory =
    is-in-hom-inclusion-hom-Subprecategory (precategory-Category C) P

  is-subcategory-Subcategory :
    is-subcategory C subtype-obj-Subcategory subtype-hom-Subcategory
  is-subcategory-Subcategory = pr2 (pr2 P)

  contains-id-Subcategory :
    contains-id-subtype-Category C
      ( subtype-obj-Subcategory)
      ( subtype-hom-Subcategory)
  contains-id-Subcategory =
    contains-id-Subprecategory (precategory-Category C) P

  is-closed-under-composition-Subcategory :
    is-closed-under-composition-subtype-Category C
      ( subtype-obj-Subcategory)
      ( subtype-hom-Subcategory)
  is-closed-under-composition-Subcategory =
    is-closed-under-composition-Subprecategory (precategory-Category C) P
```

### The precategory structure of a subcategory

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Category l1 l2)
  (P : Subcategory l3 l4 C)
  where

  hom-set-Subcategory : (x y : obj-Subcategory C P) → Set (l2 ⊔ l4)
  hom-set-Subcategory = hom-set-Subprecategory (precategory-Category C) P

  is-set-hom-Subcategory :
    (x y : obj-Subcategory C P) → is-set (hom-Subcategory C P x y)
  is-set-hom-Subcategory = is-set-hom-Subprecategory (precategory-Category C) P

  id-hom-Subcategory :
    {x : obj-Subcategory C P} → hom-Subcategory C P x x
  id-hom-Subcategory {x} = id-hom-Subprecategory (precategory-Category C) P {x}

  comp-hom-Subcategory :
    {x y z : obj-Subcategory C P} →
    hom-Subcategory C P y z →
    hom-Subcategory C P x y →
    hom-Subcategory C P x z
  comp-hom-Subcategory {x} {y} {z} =
    comp-hom-Subprecategory (precategory-Category C) P {x} {y} {z}

  associative-comp-hom-Subcategory :
    {x y z w : obj-Subcategory C P}
    (h : hom-Subcategory C P z w)
    (g : hom-Subcategory C P y z)
    (f : hom-Subcategory C P x y) →
    ( comp-hom-Subcategory {x} {y} {w}
      ( comp-hom-Subcategory {y} {z} {w} h g) f) ＝
    ( comp-hom-Subcategory {x} {z} {w} h
      ( comp-hom-Subcategory {x} {y} {z} g f))
  associative-comp-hom-Subcategory =
    associative-comp-hom-Subprecategory (precategory-Category C) P

  left-unit-law-comp-hom-Subcategory :
    {x y : obj-Subcategory C P}
    (f : hom-Subcategory C P x y) →
    comp-hom-Subcategory {x} {y} {y} (id-hom-Subcategory {y}) f ＝ f
  left-unit-law-comp-hom-Subcategory =
    left-unit-law-comp-hom-Subprecategory (precategory-Category C) P

  right-unit-law-comp-hom-Subcategory :
    {x y : obj-Subcategory C P}
    (f : hom-Subcategory C P x y) →
    comp-hom-Subcategory {x} {x} {y} f (id-hom-Subcategory {x}) ＝ f
  right-unit-law-comp-hom-Subcategory =
    right-unit-law-comp-hom-Subprecategory (precategory-Category C) P

  associative-composition-structure-Subcategory :
    associative-composition-structure-Set hom-set-Subcategory
  associative-composition-structure-Subcategory =
    associative-composition-structure-Subprecategory (precategory-Category C) P

  is-unital-composition-structure-Subcategory :
    is-unital-composition-structure-Set
      ( hom-set-Subcategory)
      ( associative-composition-structure-Subcategory)
  is-unital-composition-structure-Subcategory =
    is-unital-composition-structure-Subprecategory (precategory-Category C) P

  precategory-Subcategory : Precategory (l1 ⊔ l3) (l2 ⊔ l4)
  precategory-Subcategory =
    precategory-Subprecategory (precategory-Category C) P
```

### The category structure of a subcategory

### The inclusion functor of a subcategory

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Category l1 l2)
  (P : Subcategory l3 l4 C)
  where

  inclusion-map-Subcategory :
    map-Precategory (precategory-Subcategory C P) (precategory-Category C)
  inclusion-map-Subcategory =
    inclusion-map-Subprecategory (precategory-Category C) P

  is-functor-inclusion-Subcategory :
    is-functor-map-Precategory
      ( precategory-Subcategory C P)
      ( precategory-Category C)
      ( inclusion-map-Subcategory)
  is-functor-inclusion-Subcategory =
    is-functor-inclusion-Subprecategory (precategory-Category C) P

  inclusion-Subcategory :
    functor-Precategory (precategory-Subcategory C P) (precategory-Category C)
  inclusion-Subcategory = inclusion-Subprecategory (precategory-Category C) P
```

## Properties

### The inclusion functor is faithful and an embedding on objects

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Category l1 l2)
  (P : Subcategory l3 l4 C)
  where

  is-faithful-inclusion-Category :
    is-faithful-functor-Precategory
      ( precategory-Subcategory C P)
      ( precategory-Category C)
      ( inclusion-Subcategory C P)
  is-faithful-inclusion-Category =
    is-faithful-inclusion-Subprecategory (precategory-Category C) P

  is-emb-obj-inclusion-Category :
    is-emb
      ( obj-functor-Precategory
        ( precategory-Subcategory C P)
        ( precategory-Category C)
        ( inclusion-Subcategory C P))
  is-emb-obj-inclusion-Category =
    is-emb-obj-inclusion-Subprecategory (precategory-Category C) P

  is-embedding-inclusion-Subcategory :
    is-embedding-functor-Precategory
      ( precategory-Subcategory C P)
      ( precategory-Category C)
      ( inclusion-Subcategory C P)
  is-embedding-inclusion-Subcategory =
    is-embedding-inclusion-Subprecategory (precategory-Category C) P

  embedding-Subcategory :
    embedding-Precategory (precategory-Subcategory C P) (precategory-Category C)
  embedding-Subcategory = embedding-Subprecategory (precategory-Category C) P
```
