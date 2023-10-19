# Full subcategories

```agda
module category-theory.full-subcategories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.categories
open import category-theory.embeddings-precategories
open import category-theory.faithful-functors-precategories
open import category-theory.faithful-maps-precategories
open import category-theory.full-subprecategories
open import category-theory.fully-faithful-functors-precategories
open import category-theory.functors-categories
open import category-theory.functors-precategories
open import category-theory.isomorphisms-in-categories
open import category-theory.isomorphisms-in-precategories
open import category-theory.maps-categories
open import category-theory.maps-precategories
open import category-theory.precategories
open import category-theory.subcategories

open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.equivalences
open import foundation.function-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.subtype-identity-principle
open import foundation.subtypes
open import foundation.universe-levels
```

</details>

## Idea

A **subcategory** of a [precategory](category-theory.precategories.md) `C`
consists of a [subtype](foundation-core.subtypes.md) `P₀` of the objects of `C`.

Alternatively, we say that a [subcategory](category-theory.subcategories.md)
**is full** if for every two objects `X` and `Y` in the subcategory, the subtype
of homomorphisms from `X` to `Y` in the subcategory is
[full](foundation.full-subtypes.md).

## Definition

### Subprecategories

```agda
Full-Subcategory :
  {l1 l2 : Level} (l3 : Level) (C : Category l1 l2) → UU (l1 ⊔ lsuc l3)
Full-Subcategory l3 C = Full-Subprecategory l3 (precategory-Category C)

module _
  {l1 l2 l3 : Level}
  (C : Category l1 l2)
  (P : Full-Subcategory l3 C)
  where

  subtype-obj-Full-Subcategory : subtype l3 (obj-Category C)
  subtype-obj-Full-Subcategory = P

  obj-Full-Subcategory : UU (l1 ⊔ l3)
  obj-Full-Subcategory = type-subtype subtype-obj-Full-Subcategory

  inclusion-obj-Full-Subcategory :
    obj-Full-Subcategory → obj-Category C
  inclusion-obj-Full-Subcategory =
    inclusion-subtype subtype-obj-Full-Subcategory

  is-in-obj-Full-Subcategory : (x : obj-Category C) → UU l3
  is-in-obj-Full-Subcategory = is-in-subtype subtype-obj-Full-Subcategory

  is-prop-is-in-obj-Full-Subcategory :
    (x : obj-Category C) → is-prop (is-in-obj-Full-Subcategory x)
  is-prop-is-in-obj-Full-Subcategory =
    is-prop-is-in-subtype subtype-obj-Full-Subcategory

  is-in-obj-inclusion-obj-Full-Subcategory :
    (x : obj-Full-Subcategory) →
    is-in-obj-Full-Subcategory (inclusion-obj-Full-Subcategory x)
  is-in-obj-inclusion-obj-Full-Subcategory =
    is-in-subtype-inclusion-subtype subtype-obj-Full-Subcategory
```

### The precategory structure of a full subcategory

```agda
module _
  {l1 l2 l3 : Level}
  (C : Category l1 l2)
  (P : Full-Subcategory l3 C)
  where

  hom-set-Full-Subcategory : (x y : obj-Full-Subcategory C P) → Set l2
  hom-set-Full-Subcategory x y =
    hom-set-Category C
      ( inclusion-obj-Full-Subcategory C P x)
      ( inclusion-obj-Full-Subcategory C P y)

  hom-Full-Subcategory : (x y : obj-Full-Subcategory C P) → UU l2
  hom-Full-Subcategory x y = type-Set (hom-set-Full-Subcategory x y)

  is-set-hom-Full-Subcategory :
    (x y : obj-Full-Subcategory C P) → is-set (hom-Full-Subcategory x y)
  is-set-hom-Full-Subcategory x y =
    is-set-type-Set (hom-set-Full-Subcategory x y)

  id-hom-Full-Subcategory :
    {x : obj-Full-Subcategory C P} → hom-Full-Subcategory x x
  id-hom-Full-Subcategory = id-hom-Category C

  comp-hom-Full-Subcategory :
    {x y z : obj-Full-Subcategory C P} →
    hom-Full-Subcategory y z →
    hom-Full-Subcategory x y →
    hom-Full-Subcategory x z
  comp-hom-Full-Subcategory = comp-hom-Category C

  associative-comp-hom-Full-Subcategory :
    {x y z w : obj-Full-Subcategory C P}
    (h : hom-Full-Subcategory z w)
    (g : hom-Full-Subcategory y z)
    (f : hom-Full-Subcategory x y) →
    ( comp-hom-Full-Subcategory {x} {y} {w}
      ( comp-hom-Full-Subcategory {y} {z} {w} h g) f) ＝
    ( comp-hom-Full-Subcategory {x} {z} {w} h
      ( comp-hom-Full-Subcategory {x} {y} {z} g f))
  associative-comp-hom-Full-Subcategory =
    associative-comp-hom-Category C

  left-unit-law-comp-hom-Full-Subcategory :
    {x y : obj-Full-Subcategory C P}
    (f : hom-Full-Subcategory x y) →
    comp-hom-Full-Subcategory {x} {y} {y}
      ( id-hom-Full-Subcategory {y})
      ( f) ＝
    f
  left-unit-law-comp-hom-Full-Subcategory =
    left-unit-law-comp-hom-Category C

  right-unit-law-comp-hom-Full-Subcategory :
    {x y : obj-Full-Subcategory C P}
    (f : hom-Full-Subcategory x y) →
    comp-hom-Full-Subcategory {x} {x} {y}
      ( f)
      ( id-hom-Full-Subcategory {x}) ＝
    f
  right-unit-law-comp-hom-Full-Subcategory =
    right-unit-law-comp-hom-Category C

  associative-composition-structure-Full-Subcategory :
    associative-composition-structure-Set hom-set-Full-Subcategory
  pr1 associative-composition-structure-Full-Subcategory {x} {y} {z} =
    comp-hom-Full-Subcategory {x} {y} {z}
  pr2 associative-composition-structure-Full-Subcategory {x} {y} {z} {w} =
    associative-comp-hom-Full-Subcategory {x} {y} {z} {w}

  is-unital-composition-structure-Full-Subcategory :
    is-unital-composition-structure-Set
      ( hom-set-Full-Subcategory)
      ( associative-composition-structure-Full-Subcategory)
  pr1 is-unital-composition-structure-Full-Subcategory x =
    id-hom-Full-Subcategory {x}
  pr1 (pr2 is-unital-composition-structure-Full-Subcategory) {x} {y} =
    left-unit-law-comp-hom-Full-Subcategory {x} {y}
  pr2 (pr2 is-unital-composition-structure-Full-Subcategory) {x} {y} =
    right-unit-law-comp-hom-Full-Subcategory {x} {y}

  precategory-Full-Subcategory : Precategory (l1 ⊔ l3) l2
  pr1 precategory-Full-Subcategory = obj-Full-Subcategory C P
  pr1 (pr2 precategory-Full-Subcategory) = hom-set-Full-Subcategory
  pr1 (pr2 (pr2 precategory-Full-Subcategory)) =
    associative-composition-structure-Full-Subcategory
  pr2 (pr2 (pr2 precategory-Full-Subcategory)) =
    is-unital-composition-structure-Full-Subcategory
```

### Isomorphisms in full subcategories

```agda
module _
  {l1 l2 l3 : Level}
  (C : Category l1 l2)
  (P : Full-Subcategory l3 C)
  where

  iso-Full-Subcategory :
    (X Y : obj-Full-Subcategory C P) → UU l2
  iso-Full-Subcategory X Y =
    iso-Category C (inclusion-subtype P X) (inclusion-subtype P Y)

  iso-eq-Full-Subcategory :
    (X Y : obj-Full-Subcategory C P) → X ＝ Y → iso-Full-Subcategory X Y
  iso-eq-Full-Subcategory =
    iso-eq-Precategory (precategory-Full-Subcategory C P)
```

## Properties

### Full subcategories are categories

```agda
module _
  {l1 l2 l3 : Level}
  (C : Category l1 l2)
  (P : Full-Subcategory l3 C)
  where

  category-Full-Subcategory : Category (l1 ⊔ l3) l2
  pr1 category-Full-Subcategory = precategory-Full-Subcategory C P
  pr2 category-Full-Subcategory = is-category-precategory-Full-Subcategory C P
```

### The inclusion functor is an embedding

```agda
module _
  {l1 l2 l3 : Level}
  (C : Category l1 l2)
  (P : Full-Subcategory l3 C)
  where

  inclusion-map-Full-Subcategory :
    map-Category (category-Full-Subcategory C P) C
  pr1 inclusion-map-Full-Subcategory = inclusion-obj-Full-Subcategory C P
  pr2 inclusion-map-Full-Subcategory = id

  is-functor-inclusion-Full-Subcategory :
    is-functor-map-Category
      ( category-Full-Subcategory C P)
      ( C)
      ( inclusion-map-Full-Subcategory)
  pr1 is-functor-inclusion-Full-Subcategory g f = refl
  pr2 is-functor-inclusion-Full-Subcategory x = refl

  inclusion-Full-Subcategory :
    functor-Category (category-Full-Subcategory C P) C
  pr1 inclusion-Full-Subcategory =
    inclusion-obj-Full-Subcategory C P
  pr1 (pr2 inclusion-Full-Subcategory) = id
  pr2 (pr2 inclusion-Full-Subcategory) =
    is-functor-inclusion-Full-Subcategory

module _
  {l1 l2 l3 : Level}
  (C : Category l1 l2)
  (P : Full-Subcategory l3 C)
  where

  is-fully-faithful-inclusion-Full-Subcategory :
    is-fully-faithful-functor-Precategory
      ( precategory-Full-Subcategory C P)
      ( precategory-Category C)
      ( inclusion-Full-Subcategory C P)
  is-fully-faithful-inclusion-Full-Subcategory x y = is-equiv-id

  is-emb-obj-inclusion-Full-Subcategory :
    is-emb
      ( obj-functor-Category
        ( category-Full-Subcategory C P)
        ( C)
        ( inclusion-Full-Subcategory C P))
  is-emb-obj-inclusion-Full-Subcategory =
    is-emb-inclusion-subtype (subtype-obj-Full-Subcategory C P)

  is-embedding-inclusion-Full-Subcategory :
    is-embedding-functor-Precategory
      ( precategory-Full-Subcategory C P)
      ( precategory-Category C)
      ( inclusion-Full-Subcategory C P)
  pr1 is-embedding-inclusion-Full-Subcategory =
    is-emb-obj-inclusion-Full-Subcategory
  pr2 is-embedding-inclusion-Full-Subcategory =
    is-fully-faithful-inclusion-Full-Subcategory
```
