# Full subcategories

```agda
module category-theory.full-subcategories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.categories
open import category-theory.composition-operations-on-binary-families-of-sets
open import category-theory.embeddings-precategories
open import category-theory.full-subprecategories
open import category-theory.fully-faithful-functors-precategories
open import category-theory.functors-categories
open import category-theory.maps-categories
open import category-theory.precategories

open import foundation.dependent-pair-types
open import foundation.dependent-products-propositions
open import foundation.embeddings
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.strictly-involutive-identity-types
open import foundation.subtypes
open import foundation.universe-levels
```

</details>

## Idea

A **full subcategory** of a [precategory](category-theory.precategories.md) `C`
consists of a [subtype](foundation-core.subtypes.md) `P₀` of the objects of `C`.

Alternatively, we say that a [subcategory](category-theory.subcategories.md)
**is full** if for every two objects `X` and `Y` in the subcategory, the subtype
of morphisms from `X` to `Y` in the subcategory is
[full](foundation.full-subtypes.md).

## Definitions

### Full subcategories

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
  subtype-obj-Full-Subcategory =
    subtype-obj-Full-Subprecategory (precategory-Category C) P

  obj-Full-Subcategory : UU (l1 ⊔ l3)
  obj-Full-Subcategory = obj-Full-Subprecategory (precategory-Category C) P

  inclusion-obj-Full-Subcategory :
    obj-Full-Subcategory → obj-Category C
  inclusion-obj-Full-Subcategory =
    inclusion-obj-Full-Subprecategory (precategory-Category C) P

  is-in-obj-Full-Subcategory : (x : obj-Category C) → UU l3
  is-in-obj-Full-Subcategory =
    is-in-obj-Full-Subprecategory (precategory-Category C) P

  is-prop-is-in-obj-Full-Subcategory :
    (x : obj-Category C) → is-prop (is-in-obj-Full-Subcategory x)
  is-prop-is-in-obj-Full-Subcategory =
    is-prop-is-in-obj-Full-Subprecategory (precategory-Category C) P

  is-in-obj-inclusion-obj-Full-Subcategory :
    (x : obj-Full-Subcategory) →
    is-in-obj-Full-Subcategory (inclusion-obj-Full-Subcategory x)
  is-in-obj-inclusion-obj-Full-Subcategory =
    is-in-obj-inclusion-obj-Full-Subprecategory (precategory-Category C) P
```

### The underlying precategory of a full subcategory

```agda
module _
  {l1 l2 l3 : Level}
  (C : Category l1 l2)
  (P : Full-Subcategory l3 C)
  where

  hom-set-Full-Subcategory : (x y : obj-Full-Subcategory C P) → Set l2
  hom-set-Full-Subcategory =
    hom-set-Full-Subprecategory (precategory-Category C) P

  hom-Full-Subcategory : (x y : obj-Full-Subcategory C P) → UU l2
  hom-Full-Subcategory = hom-Full-Subprecategory (precategory-Category C) P

  is-set-hom-Full-Subcategory :
    (x y : obj-Full-Subcategory C P) → is-set (hom-Full-Subcategory x y)
  is-set-hom-Full-Subcategory =
    is-set-hom-Full-Subprecategory (precategory-Category C) P

  id-hom-Full-Subcategory :
    {x : obj-Full-Subcategory C P} → hom-Full-Subcategory x x
  id-hom-Full-Subcategory {x} =
    id-hom-Full-Subprecategory (precategory-Category C) P {x}

  comp-hom-Full-Subcategory :
    {x y z : obj-Full-Subcategory C P} →
    hom-Full-Subcategory y z →
    hom-Full-Subcategory x y →
    hom-Full-Subcategory x z
  comp-hom-Full-Subcategory {x} {y} {z} =
    comp-hom-Full-Subprecategory (precategory-Category C) P {x} {y} {z}

  associative-comp-hom-Full-Subcategory :
    {x y z w : obj-Full-Subcategory C P}
    (h : hom-Full-Subcategory z w)
    (g : hom-Full-Subcategory y z)
    (f : hom-Full-Subcategory x y) →
    comp-hom-Full-Subcategory {x} {y} {w}
      ( comp-hom-Full-Subcategory {y} {z} {w} h g)
      ( f) ＝
    comp-hom-Full-Subcategory {x} {z} {w}
      ( h)
      ( comp-hom-Full-Subcategory {x} {y} {z} g f)
  associative-comp-hom-Full-Subcategory {x} {y} {z} {w} =
    associative-comp-hom-Full-Subprecategory
      ( precategory-Category C) P {x} {y} {z} {w}

  involutive-eq-associative-comp-hom-Full-Subcategory :
    {x y z w : obj-Full-Subcategory C P}
    (h : hom-Full-Subcategory z w)
    (g : hom-Full-Subcategory y z)
    (f : hom-Full-Subcategory x y) →
    comp-hom-Full-Subcategory {x} {y} {w}
      ( comp-hom-Full-Subcategory {y} {z} {w} h g)
      ( f) ＝ⁱ
    comp-hom-Full-Subcategory {x} {z} {w}
      ( h)
      ( comp-hom-Full-Subcategory {x} {y} {z} g f)
  involutive-eq-associative-comp-hom-Full-Subcategory {x} {y} {z} {w} =
    involutive-eq-associative-comp-hom-Full-Subprecategory
      ( precategory-Category C) P {x} {y} {z} {w}

  left-unit-law-comp-hom-Full-Subcategory :
    {x y : obj-Full-Subcategory C P}
    (f : hom-Full-Subcategory x y) →
    comp-hom-Full-Subcategory {x} {y} {y}
      ( id-hom-Full-Subcategory {y})
      ( f) ＝
    f
  left-unit-law-comp-hom-Full-Subcategory {x} {y} =
    left-unit-law-comp-hom-Full-Subprecategory
      ( precategory-Category C) P {x} {y}

  right-unit-law-comp-hom-Full-Subcategory :
    {x y : obj-Full-Subcategory C P}
    (f : hom-Full-Subcategory x y) →
    comp-hom-Full-Subcategory {x} {x} {y}
      ( f)
      ( id-hom-Full-Subcategory {x}) ＝
    f
  right-unit-law-comp-hom-Full-Subcategory {x} {y} =
    right-unit-law-comp-hom-Full-Subprecategory
      ( precategory-Category C) P {x} {y}

  associative-composition-operation-Full-Subcategory :
    associative-composition-operation-binary-family-Set hom-set-Full-Subcategory
  associative-composition-operation-Full-Subcategory =
    associative-composition-operation-Full-Subprecategory
      ( precategory-Category C)
      ( P)

  is-unital-composition-operation-Full-Subcategory :
    is-unital-composition-operation-binary-family-Set
      ( hom-set-Full-Subcategory)
      ( λ {x} {y} {z} → comp-hom-Full-Subcategory {x} {y} {z})
  is-unital-composition-operation-Full-Subcategory =
    is-unital-composition-operation-Full-Subprecategory
      ( precategory-Category C)
      ( P)

  precategory-Full-Subcategory : Precategory (l1 ⊔ l3) l2
  precategory-Full-Subcategory =
    precategory-Full-Subprecategory (precategory-Category C) P
```

### Isomorphisms in full subcategories

```agda
module _
  {l1 l2 l3 : Level}
  (C : Category l1 l2)
  (P : Full-Subcategory l3 C)
  where

  iso-Full-Subcategory : (X Y : obj-Full-Subcategory C P) → UU l2
  iso-Full-Subcategory = iso-Full-Subprecategory (precategory-Category C) P

  iso-eq-Full-Subcategory :
    (X Y : obj-Full-Subcategory C P) → X ＝ Y → iso-Full-Subcategory X Y
  iso-eq-Full-Subcategory =
    iso-eq-Full-Subprecategory (precategory-Category C) P
```

### The underlying category of a full subcategory

```agda
module _
  {l1 l2 l3 : Level}
  (C : Category l1 l2)
  (P : Full-Subcategory l3 C)
  where

  is-category-precategory-Full-Subcategory :
    is-category-Precategory (precategory-Full-Subcategory C P)
  is-category-precategory-Full-Subcategory =
    is-category-precategory-is-category-Full-Subprecategory
      ( precategory-Category C) P (is-category-Category C)

  category-Full-Subcategory : Category (l1 ⊔ l3) l2
  pr1 category-Full-Subcategory = precategory-Full-Subcategory C P
  pr2 category-Full-Subcategory = is-category-precategory-Full-Subcategory
```

## Properties

### The inclusion functor is an embedding

```agda
module _
  {l1 l2 l3 : Level}
  (C : Category l1 l2)
  (P : Full-Subcategory l3 C)
  where

  inclusion-map-Full-Subcategory :
    map-Category (category-Full-Subcategory C P) C
  inclusion-map-Full-Subcategory =
    inclusion-map-Full-Subprecategory (precategory-Category C) P

  is-functor-inclusion-Full-Subcategory :
    is-functor-map-Category
      ( category-Full-Subcategory C P)
      ( C)
      ( inclusion-map-Full-Subcategory)
  is-functor-inclusion-Full-Subcategory =
    is-functor-inclusion-Full-Subprecategory (precategory-Category C) P

  inclusion-Full-Subcategory :
    functor-Category (category-Full-Subcategory C P) C
  inclusion-Full-Subcategory =
    inclusion-Full-Subprecategory (precategory-Category C) P

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
  is-fully-faithful-inclusion-Full-Subcategory =
    is-fully-faithful-inclusion-Full-Subprecategory (precategory-Category C) P

  is-emb-obj-inclusion-Full-Subcategory :
    is-emb
      ( obj-functor-Category
        ( category-Full-Subcategory C P)
        ( C)
        ( inclusion-Full-Subcategory C P))
  is-emb-obj-inclusion-Full-Subcategory =
    is-emb-obj-inclusion-Full-Subprecategory (precategory-Category C) P

  is-embedding-inclusion-Full-Subcategory :
    is-embedding-functor-Precategory
      ( precategory-Full-Subcategory C P)
      ( precategory-Category C)
      ( inclusion-Full-Subcategory C P)
  is-embedding-inclusion-Full-Subcategory =
    is-embedding-inclusion-Full-Subprecategory (precategory-Category C) P

  embedding-Full-Subcategory :
    embedding-Precategory
      ( precategory-Full-Subcategory C P)
      ( precategory-Category C)
  embedding-Full-Subcategory =
    embedding-Full-Subprecategory (precategory-Category C) P
```
