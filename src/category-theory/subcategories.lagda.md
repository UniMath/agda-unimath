# Subcategories

```agda
open import foundation.function-extensionality-axiom

module
  category-theory.subcategories
  (funext : function-extensionality)
  where
```

<details><summary>Imports</summary>

```agda
open import category-theory.categories funext
open import category-theory.composition-operations-on-binary-families-of-sets funext
open import category-theory.faithful-functors-precategories funext
open import category-theory.functors-precategories funext
open import category-theory.isomorphisms-in-categories funext
open import category-theory.isomorphisms-in-precategories funext
open import category-theory.isomorphisms-in-subprecategories funext
open import category-theory.maps-precategories funext
open import category-theory.precategories funext
open import category-theory.replete-subprecategories funext
open import category-theory.subprecategories funext

open import foundation.contractible-types funext
open import foundation.dependent-pair-types
open import foundation.embeddings funext
open import foundation.equivalences funext
open import foundation.functoriality-dependent-pair-types funext
open import foundation.fundamental-theorem-of-identity-types
open import foundation.identity-types funext
open import foundation.propositions funext
open import foundation.sets funext
open import foundation.strictly-involutive-identity-types funext
open import foundation.subtype-identity-principle
open import foundation.subtypes funext
open import foundation.universe-levels
```

</details>

## Idea

A **subcategory** of a [category](category-theory.categories.md) `C` is a
[subprecategory](category-theory.subprecategories.md). It consists of a
[subtype](foundation-core.subtypes.md) `P₀` of the objects of `C`, and a family
of subtypes

```text
  P₁ : (X Y : obj C) → P₀ X → P₀ Y → subtype (hom X Y)
```

of the morphisms of `C`, such that `P₁` contains all identity morphisms of
objects in `P₀` and is closed under composition. By univalence, it therefore
contains the isomorphisms, and hence defines a category.

## Definitions

### Sub-hom-families of categories

```agda
subtype-hom-Category :
  {l1 l2 l3 : Level} (l4 : Level)
  (C : Category l1 l2)
  (P₀ : subtype l3 (obj-Category C)) → UU (l1 ⊔ l2 ⊔ l3 ⊔ lsuc l4)
subtype-hom-Category l4 C = subtype-hom-Precategory l4 (precategory-Category C)
```

### Categorical predicates on sub-hom-families of categories

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Category l1 l2)
  (P₀ : subtype l3 (obj-Category C))
  (P₁ : subtype-hom-Category l4 C P₀)
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
  (P₁ : subtype-hom-Category l4 C P₀)
  where

  is-subcategory-Prop : Prop (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  is-subcategory-Prop = is-subprecategory-Prop (precategory-Category C) P₀ P₁

  is-subcategory : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  is-subcategory = type-Prop is-subcategory-Prop

  is-prop-is-subcategory : is-prop (is-subcategory)
  is-prop-is-subcategory = is-prop-type-Prop is-subcategory-Prop

  contains-id-is-subcategory :
    is-subcategory →
    contains-id-subtype-Category C P₀ P₁
  contains-id-is-subcategory =
    contains-id-is-subprecategory (precategory-Category C) P₀ P₁

  is-closed-under-composition-is-subcategory :
    is-subcategory →
    is-closed-under-composition-subtype-Category C P₀ P₁
  is-closed-under-composition-is-subcategory =
    is-closed-under-composition-is-subprecategory (precategory-Category C) P₀ P₁
```

### Subcategories

```agda
Subcategory :
  {l1 l2 : Level} (l3 l4 : Level)
  (C : Category l1 l2) →
  UU (l1 ⊔ l2 ⊔ lsuc l3 ⊔ lsuc l4)
Subcategory l3 l4 C = Subprecategory l3 l4 (precategory-Category C)
```

#### Objects in subcategories

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Category l1 l2)
  (P : Subcategory l3 l4 C)
  where

  subtype-obj-Subcategory : subtype l3 (obj-Category C)
  subtype-obj-Subcategory =
    subtype-obj-Subprecategory (precategory-Category C) P

  obj-Subcategory : UU (l1 ⊔ l3)
  obj-Subcategory = type-subtype subtype-obj-Subcategory

  inclusion-obj-Subcategory : obj-Subcategory → obj-Category C
  inclusion-obj-Subcategory = inclusion-subtype subtype-obj-Subcategory

  is-in-obj-Subcategory : (x : obj-Category C) → UU l3
  is-in-obj-Subcategory = is-in-subtype subtype-obj-Subcategory

  is-prop-is-in-obj-Subcategory :
    (x : obj-Category C) → is-prop (is-in-obj-Subcategory x)
  is-prop-is-in-obj-Subcategory =
    is-prop-is-in-subtype subtype-obj-Subcategory

  is-in-obj-inclusion-obj-Subcategory :
    (x : obj-Subcategory) →
    is-in-obj-Subcategory (inclusion-obj-Subcategory x)
  is-in-obj-inclusion-obj-Subcategory =
    is-in-subtype-inclusion-subtype subtype-obj-Subcategory
```

#### Morphisms in subcategories

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Category l1 l2)
  (P : Subcategory l3 l4 C)
  where

  subtype-hom-Subcategory :
    subtype-hom-Category l4 C (subtype-obj-Subcategory C P)
  subtype-hom-Subcategory =
    subtype-hom-Subprecategory (precategory-Category C) P

  subtype-hom-obj-subcategory-Subcategory :
    (x y : obj-Subcategory C P) →
    subtype l4
      ( hom-Category C
        ( inclusion-obj-Subcategory C P x)
        ( inclusion-obj-Subcategory C P y))
  subtype-hom-obj-subcategory-Subcategory =
    subtype-hom-obj-subprecategory-Subprecategory (precategory-Category C) P

  hom-Subcategory : (x y : obj-Subcategory C P) → UU (l2 ⊔ l4)
  hom-Subcategory x y =
    type-subtype (subtype-hom-obj-subcategory-Subcategory x y)

  inclusion-hom-Subcategory :
    (x y : obj-Subcategory C P) →
    hom-Subcategory x y →
    hom-Category C
      ( inclusion-obj-Subcategory C P x)
      ( inclusion-obj-Subcategory C P y)
  inclusion-hom-Subcategory x y =
    inclusion-subtype (subtype-hom-obj-subcategory-Subcategory x y)
```

The predicate on morphisms between subobjects of being contained in the
subcategory:

```agda
  is-in-hom-obj-subcategory-Subcategory :
    ( x y : obj-Subcategory C P) →
    hom-Category C
      ( inclusion-obj-Subcategory C P x)
      ( inclusion-obj-Subcategory C P y) →
    UU l4
  is-in-hom-obj-subcategory-Subcategory x y =
    is-in-subtype (subtype-hom-obj-subcategory-Subcategory x y)

  is-prop-is-in-hom-obj-subcategory-Subcategory :
    ( x y : obj-Subcategory C P)
    ( f :
      hom-Category C
        ( inclusion-obj-Subcategory C P x)
        ( inclusion-obj-Subcategory C P y)) →
    is-prop (is-in-hom-obj-subcategory-Subcategory x y f)
  is-prop-is-in-hom-obj-subcategory-Subcategory x y =
    is-prop-is-in-subtype (subtype-hom-obj-subcategory-Subcategory x y)
```

The predicate on morphisms between any objects of being contained in the
subcategory:

```agda
  is-in-hom-Subcategory :
    (x y : obj-Category C) (f : hom-Category C x y) → UU (l3 ⊔ l4)
  is-in-hom-Subcategory =
    is-in-hom-Subprecategory (precategory-Category C) P

  is-prop-is-in-hom-Subcategory :
    (x y : obj-Category C) (f : hom-Category C x y) →
    is-prop (is-in-hom-Subcategory x y f)
  is-prop-is-in-hom-Subcategory =
    is-prop-is-in-hom-Subprecategory (precategory-Category C) P

  is-in-hom-obj-subcategory-inclusion-hom-Subcategory :
    (x y : obj-Subcategory C P)
    (f : hom-Subcategory x y) →
    is-in-hom-obj-subcategory-Subcategory x y
      ( inclusion-hom-Subcategory x y f)
  is-in-hom-obj-subcategory-inclusion-hom-Subcategory =
    is-in-hom-obj-subprecategory-inclusion-hom-Subprecategory
      ( precategory-Category C) P

  is-in-hom-inclusion-hom-Subcategory :
    (x y : obj-Subcategory C P)
    (f : hom-Subcategory x y) →
    is-in-hom-Subcategory
      ( inclusion-obj-Subcategory C P x)
      ( inclusion-obj-Subcategory C P y)
      ( inclusion-hom-Subcategory x y f)
  is-in-hom-inclusion-hom-Subcategory =
    is-in-hom-inclusion-hom-Subprecategory (precategory-Category C) P
```

#### Subcategories are subcategories

```agda
  is-subcategory-Subcategory :
    is-subcategory C
      ( subtype-obj-Subcategory C P) (subtype-hom-Subcategory)
  is-subcategory-Subcategory =
    is-subprecategory-Subprecategory (precategory-Category C) P

  contains-id-Subcategory :
    contains-id-subtype-Category C
      ( subtype-obj-Subcategory C P)
      ( subtype-hom-Subcategory)
  contains-id-Subcategory =
    contains-id-Subprecategory (precategory-Category C) P

  is-closed-under-composition-Subcategory :
    is-closed-under-composition-subtype-Category C
      ( subtype-obj-Subcategory C P)
      ( subtype-hom-Subcategory)
  is-closed-under-composition-Subcategory =
    is-closed-under-composition-Subprecategory (precategory-Category C) P
```

### The underlying precategory of a subcategory

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Category l1 l2)
  (P : Subcategory l3 l4 C)
  where

  hom-set-Subcategory : (x y : obj-Subcategory C P) → Set (l2 ⊔ l4)
  hom-set-Subcategory =
    hom-set-Subprecategory (precategory-Category C) P

  is-set-hom-Subcategory :
    (x y : obj-Subcategory C P) → is-set (hom-Subcategory C P x y)
  is-set-hom-Subcategory x y = is-set-type-Set (hom-set-Subcategory x y)

  id-hom-Subcategory :
    {x : obj-Subcategory C P} → hom-Subcategory C P x x
  id-hom-Subcategory =
    id-hom-Subprecategory (precategory-Category C) P

  comp-hom-Subcategory :
    {x y z : obj-Subcategory C P} →
    hom-Subcategory C P y z →
    hom-Subcategory C P x y →
    hom-Subcategory C P x z
  comp-hom-Subcategory =
    comp-hom-Subprecategory (precategory-Category C) P

  associative-comp-hom-Subcategory :
    {x y z w : obj-Subcategory C P}
    (h : hom-Subcategory C P z w)
    (g : hom-Subcategory C P y z)
    (f : hom-Subcategory C P x y) →
    comp-hom-Subcategory {x} {y} {w}
      ( comp-hom-Subcategory {y} {z} {w} h g)
      ( f) ＝
    comp-hom-Subcategory {x} {z} {w}
      ( h)
      ( comp-hom-Subcategory {x} {y} {z} g f)
  associative-comp-hom-Subcategory =
    associative-comp-hom-Subprecategory (precategory-Category C) P

  involutive-eq-associative-comp-hom-Subcategory :
    {x y z w : obj-Subcategory C P}
    (h : hom-Subcategory C P z w)
    (g : hom-Subcategory C P y z)
    (f : hom-Subcategory C P x y) →
    comp-hom-Subcategory {x} {y} {w}
      ( comp-hom-Subcategory {y} {z} {w} h g)
      ( f) ＝ⁱ
    comp-hom-Subcategory {x} {z} {w}
      ( h)
      ( comp-hom-Subcategory {x} {y} {z} g f)
  involutive-eq-associative-comp-hom-Subcategory =
    involutive-eq-associative-comp-hom-Subprecategory (precategory-Category C) P

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

  associative-composition-operation-Subcategory :
    associative-composition-operation-binary-family-Set hom-set-Subcategory
  associative-composition-operation-Subcategory =
    associative-composition-operation-Subprecategory (precategory-Category C) P

  is-unital-composition-operation-Subcategory :
    is-unital-composition-operation-binary-family-Set
      ( hom-set-Subcategory)
      ( comp-hom-Subcategory)
  is-unital-composition-operation-Subcategory =
    is-unital-composition-operation-Subprecategory (precategory-Category C) P

  precategory-Subcategory : Precategory (l1 ⊔ l3) (l2 ⊔ l4)
  precategory-Subcategory =
    precategory-Subprecategory (precategory-Category C) P
```

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

### Subcategories are replete

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Category l1 l2)
  (P : Subcategory l3 l4 C)
  where

  is-replete-Subcategory : is-replete-Subprecategory (precategory-Category C) P
  is-replete-Subcategory =
    is-replete-subprecategory-is-category-Subprecategory
      ( precategory-Category C)
      ( P)
      ( is-category-Category C)

  compute-iso-Subcategory :
    {x y : obj-Subcategory C P} →
    iso-Category C
      ( inclusion-obj-Subcategory C P x)
      ( inclusion-obj-Subcategory C P y) ≃
    iso-Subprecategory (precategory-Category C) P x y
  compute-iso-Subcategory {x} {y} =
    compute-iso-is-replete-Subprecategory
      ( precategory-Category C) P is-replete-Subcategory x y

  inv-compute-iso-Subcategory :
    {x y : obj-Subcategory C P} →
    iso-Subprecategory (precategory-Category C) P x y ≃
    iso-Category C
      ( inclusion-obj-Subcategory C P x)
      ( inclusion-obj-Subcategory C P y)
  inv-compute-iso-Subcategory {x} {y} =
    inv-compute-iso-is-replete-Subprecategory
      ( precategory-Category C) P is-replete-Subcategory x y
```

### Subcategories are categories

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Category l1 l2)
  (P : Subcategory l3 l4 C)
  where

  is-category-Subcategory :
    is-category-Precategory (precategory-Subcategory C P)
  is-category-Subcategory x =
    fundamental-theorem-id
      ( is-contr-equiv _
        ( equiv-tot (λ y → inv-compute-iso-Subcategory C P {x} {y}))
        ( is-torsorial-Eq-subtype
          ( is-torsorial-iso-Category C (inclusion-obj-Subcategory C P x))
          ( is-prop-is-in-obj-Subcategory C P)
          ( inclusion-obj-Subcategory C P x)
          ( id-iso-Category C)
          ( is-in-obj-inclusion-obj-Subcategory C P x)))
      ( iso-eq-Precategory (precategory-Subcategory C P) x)

  category-Subcategory : Category (l1 ⊔ l3) (l2 ⊔ l4)
  pr1 category-Subcategory = precategory-Subcategory C P
  pr2 category-Subcategory = is-category-Subcategory
```

### The inclusion functor is an embedding on objects and hom-sets

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Category l1 l2)
  (P : Subcategory l3 l4 C)
  where

  is-faithful-inclusion-Subcategory :
    is-faithful-functor-Precategory
      ( precategory-Subcategory C P)
      ( precategory-Category C)
      ( inclusion-Subcategory C P)
  is-faithful-inclusion-Subcategory =
    is-faithful-inclusion-Subprecategory (precategory-Category C) P

  is-emb-obj-inclusion-Subcategory :
    is-emb
      ( obj-functor-Precategory
        ( precategory-Subcategory C P)
        ( precategory-Category C)
        ( inclusion-Subcategory C P))
  is-emb-obj-inclusion-Subcategory =
    is-emb-obj-inclusion-Subprecategory (precategory-Category C) P
```

### The inclusion functor is pseudomonic

This is another consequence of repleteness.

## External links

- [Univalent Subcategories](https://1lab.dev/Cat.Functor.Subcategory.html#univalent-subcategories)
  at 1lab
