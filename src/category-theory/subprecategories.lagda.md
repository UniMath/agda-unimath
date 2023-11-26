# Subprecategories

```agda
module category-theory.subprecategories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.composition-operations-on-binary-families-of-sets
open import category-theory.faithful-functors-precategories
open import category-theory.functors-precategories
open import category-theory.maps-precategories
open import category-theory.precategories

open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.identity-types
open import foundation.iterated-dependent-product-types
open import foundation.propositions
open import foundation.sets
open import foundation.subtypes
open import foundation.universe-levels
```

</details>

## Idea

A **subprecategory** of a [precategory](category-theory.precategories.md) `C`
consists of a [subtype](foundation-core.subtypes.md) `P₀` of the objects of `C`,
and a family of subtypes `P₁`

```text
  P₁ : (X Y : obj C) → P₀ X → P₀ Y → subtype (hom X Y)
```

of the morphisms of `C`, such that `P₁` contains all identity morphisms of
objects in `P₀` and is closed under composition.

## Definition

### Sub-hom-families

```agda
subtype-hom-Precategory :
  {l1 l2 l3 : Level} (l4 : Level)
  (C : Precategory l1 l2)
  (P₀ : subtype l3 (obj-Precategory C)) → UU (l1 ⊔ l2 ⊔ l3 ⊔ lsuc l4)
subtype-hom-Precategory l4 C P₀ =
  (x y : obj-Precategory C) → is-in-subtype P₀ x → is-in-subtype P₀ y →
  subtype l4 (hom-Precategory C x y)
```

### Categorical predicates on sub-hom-families

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2)
  (P₀ : subtype l3 (obj-Precategory C))
  (P₁ : subtype-hom-Precategory l4 C P₀)
  where

  contains-id-subtype-Precategory : UU (l1 ⊔ l3 ⊔ l4)
  contains-id-subtype-Precategory =
    (x : obj-Precategory C) →
    (x₀ : is-in-subtype P₀ x) →
    is-in-subtype (P₁ x x x₀ x₀) (id-hom-Precategory C)

  is-prop-contains-id-subtype-Precategory :
    is-prop contains-id-subtype-Precategory
  is-prop-contains-id-subtype-Precategory =
    is-prop-iterated-Π 2
      ( λ x x₀ → is-prop-is-in-subtype (P₁ x x x₀ x₀) (id-hom-Precategory C))

  contains-id-prop-subtype-Precategory : Prop (l1 ⊔ l3 ⊔ l4)
  pr1 contains-id-prop-subtype-Precategory =
    contains-id-subtype-Precategory
  pr2 contains-id-prop-subtype-Precategory =
    is-prop-contains-id-subtype-Precategory

  is-closed-under-composition-subtype-Precategory : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  is-closed-under-composition-subtype-Precategory =
    (x y z : obj-Precategory C) →
    (g : hom-Precategory C y z) →
    (f : hom-Precategory C x y) →
    (x₀ : is-in-subtype P₀ x) →
    (y₀ : is-in-subtype P₀ y) →
    (z₀ : is-in-subtype P₀ z) →
    is-in-subtype (P₁ y z y₀ z₀) g →
    is-in-subtype (P₁ x y x₀ y₀) f →
    is-in-subtype (P₁ x z x₀ z₀) (comp-hom-Precategory C g f)

  is-prop-is-closed-under-composition-subtype-Precategory :
    is-prop is-closed-under-composition-subtype-Precategory
  is-prop-is-closed-under-composition-subtype-Precategory =
    is-prop-iterated-Π 10
      ( λ x y z g f x₀ _ z₀ _ _ →
        is-prop-is-in-subtype (P₁ x z x₀ z₀) (comp-hom-Precategory C g f))

  is-closed-under-composition-prop-subtype-Precategory :
    Prop (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  pr1 is-closed-under-composition-prop-subtype-Precategory =
    is-closed-under-composition-subtype-Precategory
  pr2 is-closed-under-composition-prop-subtype-Precategory =
    is-prop-is-closed-under-composition-subtype-Precategory
```

### The predicate of being a subprecategory

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2)
  (P₀ : subtype l3 (obj-Precategory C))
  (P₁ : subtype-hom-Precategory l4 C P₀)
  where

  is-subprecategory-Prop : Prop (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  is-subprecategory-Prop =
    prod-Prop
      ( contains-id-prop-subtype-Precategory C P₀ P₁)
      ( is-closed-under-composition-prop-subtype-Precategory C P₀ P₁)

  is-subprecategory : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  is-subprecategory = type-Prop is-subprecategory-Prop

  is-prop-is-subprecategory : is-prop (is-subprecategory)
  is-prop-is-subprecategory = is-prop-type-Prop is-subprecategory-Prop

  contains-id-is-subprecategory :
    is-subprecategory → contains-id-subtype-Precategory C P₀ P₁
  contains-id-is-subprecategory = pr1

  is-closed-under-composition-is-subprecategory :
    is-subprecategory → is-closed-under-composition-subtype-Precategory C P₀ P₁
  is-closed-under-composition-is-subprecategory = pr2
```

### Subprecategories

```agda
Subprecategory :
  {l1 l2 : Level} (l3 l4 : Level)
  (C : Precategory l1 l2) →
  UU (l1 ⊔ l2 ⊔ lsuc l3 ⊔ lsuc l4)
Subprecategory l3 l4 C =
  Σ ( subtype l3 (obj-Precategory C))
    ( λ P₀ →
      Σ ( subtype-hom-Precategory l4 C P₀)
        ( is-subprecategory C P₀))
```

#### Objects in subprecategories

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2)
  (P : Subprecategory l3 l4 C)
  where

  subtype-obj-Subprecategory : subtype l3 (obj-Precategory C)
  subtype-obj-Subprecategory = pr1 P

  obj-Subprecategory : UU (l1 ⊔ l3)
  obj-Subprecategory = type-subtype subtype-obj-Subprecategory

  inclusion-obj-Subprecategory : obj-Subprecategory → obj-Precategory C
  inclusion-obj-Subprecategory = inclusion-subtype subtype-obj-Subprecategory

  is-in-obj-Subprecategory : (x : obj-Precategory C) → UU l3
  is-in-obj-Subprecategory = is-in-subtype subtype-obj-Subprecategory

  is-prop-is-in-obj-Subprecategory :
    (x : obj-Precategory C) → is-prop (is-in-obj-Subprecategory x)
  is-prop-is-in-obj-Subprecategory =
    is-prop-is-in-subtype subtype-obj-Subprecategory

  is-in-obj-inclusion-obj-Subprecategory :
    (x : obj-Subprecategory) →
    is-in-obj-Subprecategory (inclusion-obj-Subprecategory x)
  is-in-obj-inclusion-obj-Subprecategory =
    is-in-subtype-inclusion-subtype subtype-obj-Subprecategory
```

#### Morphisms in subprecategories

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2)
  (P : Subprecategory l3 l4 C)
  where

  subtype-hom-Subprecategory :
    subtype-hom-Precategory l4 C (subtype-obj-Subprecategory C P)
  subtype-hom-Subprecategory = pr1 (pr2 P)

  subtype-hom-obj-subprecategory-Subprecategory :
    (x y : obj-Subprecategory C P) →
    subtype l4
      ( hom-Precategory C
        ( inclusion-obj-Subprecategory C P x)
        ( inclusion-obj-Subprecategory C P y))
  subtype-hom-obj-subprecategory-Subprecategory x y =
    subtype-hom-Subprecategory
      ( inclusion-obj-Subprecategory C P x)
      ( inclusion-obj-Subprecategory C P y)
      ( is-in-obj-inclusion-obj-Subprecategory C P x)
      ( is-in-obj-inclusion-obj-Subprecategory C P y)

  hom-Subprecategory : (x y : obj-Subprecategory C P) → UU (l2 ⊔ l4)
  hom-Subprecategory x y =
    type-subtype (subtype-hom-obj-subprecategory-Subprecategory x y)

  inclusion-hom-Subprecategory :
    (x y : obj-Subprecategory C P) →
    hom-Subprecategory x y →
    hom-Precategory C
      ( inclusion-obj-Subprecategory C P x)
      ( inclusion-obj-Subprecategory C P y)
  inclusion-hom-Subprecategory x y =
    inclusion-subtype (subtype-hom-obj-subprecategory-Subprecategory x y)
```

The predicate on a morphism between subobjects of being contained in the
subprecategory:

```agda
  is-in-hom-obj-subprecategory-Subprecategory :
    ( x y : obj-Subprecategory C P) →
    hom-Precategory C
      ( inclusion-obj-Subprecategory C P x)
      ( inclusion-obj-Subprecategory C P y) →
    UU l4
  is-in-hom-obj-subprecategory-Subprecategory x y =
    is-in-subtype (subtype-hom-obj-subprecategory-Subprecategory x y)

  is-prop-is-in-hom-obj-subprecategory-Subprecategory :
    ( x y : obj-Subprecategory C P)
    ( f :
      hom-Precategory C
        ( inclusion-obj-Subprecategory C P x)
        ( inclusion-obj-Subprecategory C P y)) →
    is-prop (is-in-hom-obj-subprecategory-Subprecategory x y f)
  is-prop-is-in-hom-obj-subprecategory-Subprecategory x y =
    is-prop-is-in-subtype (subtype-hom-obj-subprecategory-Subprecategory x y)
```

The predicate on a morphism between any objects of being contained in the
subprecategory:

```agda
  is-in-hom-Subprecategory :
    (x y : obj-Precategory C) (f : hom-Precategory C x y) → UU (l3 ⊔ l4)
  is-in-hom-Subprecategory x y f =
    Σ ( is-in-obj-Subprecategory C P x)
      ( λ x₀ →
        Σ ( is-in-obj-Subprecategory C P y)
          ( λ y₀ →
            is-in-hom-obj-subprecategory-Subprecategory (x , x₀) (y , y₀) f))

  is-prop-is-in-hom-Subprecategory :
    (x y : obj-Precategory C) (f : hom-Precategory C x y) →
    is-prop (is-in-hom-Subprecategory x y f)
  is-prop-is-in-hom-Subprecategory x y f =
    is-prop-Σ
      ( is-prop-is-in-obj-Subprecategory C P x)
      ( λ x₀ →
        is-prop-Σ
          ( is-prop-is-in-obj-Subprecategory C P y)
          ( λ y₀ →
            is-prop-is-in-hom-obj-subprecategory-Subprecategory
              ( x , x₀) (y , y₀) f))

  is-in-hom-obj-subprecategory-inclusion-hom-Subprecategory :
    (x y : obj-Subprecategory C P)
    (f : hom-Subprecategory x y) →
    is-in-hom-obj-subprecategory-Subprecategory x y
      ( inclusion-hom-Subprecategory x y f)
  is-in-hom-obj-subprecategory-inclusion-hom-Subprecategory x y f = pr2 f

  is-in-hom-inclusion-hom-Subprecategory :
    (x y : obj-Subprecategory C P)
    (f : hom-Subprecategory x y) →
    is-in-hom-Subprecategory
      ( inclusion-obj-Subprecategory C P x)
      ( inclusion-obj-Subprecategory C P y)
      ( inclusion-hom-Subprecategory x y f)
  pr1 (is-in-hom-inclusion-hom-Subprecategory x y f) =
    is-in-obj-inclusion-obj-Subprecategory C P x
  pr1 (pr2 (is-in-hom-inclusion-hom-Subprecategory x y f)) =
    is-in-obj-inclusion-obj-Subprecategory C P y
  pr2 (pr2 (is-in-hom-inclusion-hom-Subprecategory x y f)) =
    is-in-hom-obj-subprecategory-inclusion-hom-Subprecategory x y f
```

#### Subprecategories are subprecategories

```agda
  is-subprecategory-Subprecategory :
    is-subprecategory C
      ( subtype-obj-Subprecategory C P) (subtype-hom-Subprecategory)
  is-subprecategory-Subprecategory = pr2 (pr2 P)

  contains-id-Subprecategory :
    contains-id-subtype-Precategory C
      ( subtype-obj-Subprecategory C P)
      ( subtype-hom-Subprecategory)
  contains-id-Subprecategory =
    contains-id-is-subprecategory C
      ( subtype-obj-Subprecategory C P)
      ( subtype-hom-Subprecategory)
      ( is-subprecategory-Subprecategory)

  is-closed-under-composition-Subprecategory :
    is-closed-under-composition-subtype-Precategory C
      ( subtype-obj-Subprecategory C P)
      ( subtype-hom-Subprecategory)
  is-closed-under-composition-Subprecategory =
    is-closed-under-composition-is-subprecategory C
      ( subtype-obj-Subprecategory C P)
      ( subtype-hom-Subprecategory)
      ( is-subprecategory-Subprecategory)
```

### The underlying precategory of a subprecategory

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2)
  (P : Subprecategory l3 l4 C)
  where

  hom-set-Subprecategory : (x y : obj-Subprecategory C P) → Set (l2 ⊔ l4)
  hom-set-Subprecategory x y =
    set-subset
      ( hom-set-Precategory C
        ( inclusion-obj-Subprecategory C P x)
        ( inclusion-obj-Subprecategory C P y))
      ( subtype-hom-obj-subprecategory-Subprecategory C P x y)

  is-set-hom-Subprecategory :
    (x y : obj-Subprecategory C P) → is-set (hom-Subprecategory C P x y)
  is-set-hom-Subprecategory x y = is-set-type-Set (hom-set-Subprecategory x y)

  id-hom-Subprecategory :
    {x : obj-Subprecategory C P} → hom-Subprecategory C P x x
  pr1 (id-hom-Subprecategory) = id-hom-Precategory C
  pr2 (id-hom-Subprecategory {x}) =
    contains-id-Subprecategory C P
      ( inclusion-obj-Subprecategory C P x)
      ( is-in-obj-inclusion-obj-Subprecategory C P x)

  comp-hom-Subprecategory :
    {x y z : obj-Subprecategory C P} →
    hom-Subprecategory C P y z →
    hom-Subprecategory C P x y →
    hom-Subprecategory C P x z
  pr1 (comp-hom-Subprecategory {x} {y} {z} g f) =
    comp-hom-Precategory C
      ( inclusion-hom-Subprecategory C P y z g)
      ( inclusion-hom-Subprecategory C P x y f)
  pr2 (comp-hom-Subprecategory {x} {y} {z} g f) =
    is-closed-under-composition-Subprecategory C P
      ( inclusion-obj-Subprecategory C P x)
      ( inclusion-obj-Subprecategory C P y)
      ( inclusion-obj-Subprecategory C P z)
      ( inclusion-hom-Subprecategory C P y z g)
      ( inclusion-hom-Subprecategory C P x y f)
      ( is-in-obj-inclusion-obj-Subprecategory C P x)
      ( is-in-obj-inclusion-obj-Subprecategory C P y)
      ( is-in-obj-inclusion-obj-Subprecategory C P z)
      ( pr2 g)
      ( pr2 f)

  associative-comp-hom-Subprecategory :
    {x y z w : obj-Subprecategory C P}
    (h : hom-Subprecategory C P z w)
    (g : hom-Subprecategory C P y z)
    (f : hom-Subprecategory C P x y) →
    comp-hom-Subprecategory {x} {y} {w}
      ( comp-hom-Subprecategory {y} {z} {w} h g)
      ( f) ＝
    comp-hom-Subprecategory {x} {z} {w}
      ( h)
      ( comp-hom-Subprecategory {x} {y} {z} g f)
  associative-comp-hom-Subprecategory {x} {y} {z} {w} h g f =
    eq-type-subtype
      ( subtype-hom-Subprecategory C P
        ( inclusion-obj-Subprecategory C P x)
        ( inclusion-obj-Subprecategory C P w)
        ( is-in-obj-inclusion-obj-Subprecategory C P x)
        ( is-in-obj-inclusion-obj-Subprecategory C P w))
      ( associative-comp-hom-Precategory C
        ( inclusion-hom-Subprecategory C P z w h)
        ( inclusion-hom-Subprecategory C P y z g)
        ( inclusion-hom-Subprecategory C P x y f))

  inv-associative-comp-hom-Subprecategory :
    {x y z w : obj-Subprecategory C P}
    (h : hom-Subprecategory C P z w)
    (g : hom-Subprecategory C P y z)
    (f : hom-Subprecategory C P x y) →
    ( comp-hom-Subprecategory {x} {z} {w} h
      ( comp-hom-Subprecategory {x} {y} {z} g f)) ＝
    ( comp-hom-Subprecategory {x} {y} {w}
      ( comp-hom-Subprecategory {y} {z} {w} h g) f)
  inv-associative-comp-hom-Subprecategory {x} {y} {z} {w} h g f =
    eq-type-subtype
      ( subtype-hom-Subprecategory C P
        ( inclusion-obj-Subprecategory C P x)
        ( inclusion-obj-Subprecategory C P w)
        ( is-in-obj-inclusion-obj-Subprecategory C P x)
        ( is-in-obj-inclusion-obj-Subprecategory C P w))
      ( inv-associative-comp-hom-Precategory C
        ( inclusion-hom-Subprecategory C P z w h)
        ( inclusion-hom-Subprecategory C P y z g)
        ( inclusion-hom-Subprecategory C P x y f))

  left-unit-law-comp-hom-Subprecategory :
    {x y : obj-Subprecategory C P}
    (f : hom-Subprecategory C P x y) →
    comp-hom-Subprecategory {x} {y} {y} (id-hom-Subprecategory {y}) f ＝ f
  left-unit-law-comp-hom-Subprecategory {x} {y} f =
    eq-type-subtype
      ( subtype-hom-Subprecategory C P
        ( inclusion-obj-Subprecategory C P x)
        ( inclusion-obj-Subprecategory C P y)
        ( is-in-obj-inclusion-obj-Subprecategory C P x)
        ( is-in-obj-inclusion-obj-Subprecategory C P y))
      ( left-unit-law-comp-hom-Precategory C
        ( inclusion-hom-Subprecategory C P x y f))

  right-unit-law-comp-hom-Subprecategory :
    {x y : obj-Subprecategory C P}
    (f : hom-Subprecategory C P x y) →
    comp-hom-Subprecategory {x} {x} {y} f (id-hom-Subprecategory {x}) ＝ f
  right-unit-law-comp-hom-Subprecategory {x} {y} f =
    eq-type-subtype
      ( subtype-hom-Subprecategory C P
        ( inclusion-obj-Subprecategory C P x)
        ( inclusion-obj-Subprecategory C P y)
        ( is-in-obj-inclusion-obj-Subprecategory C P x)
        ( is-in-obj-inclusion-obj-Subprecategory C P y))
      ( right-unit-law-comp-hom-Precategory C
        ( inclusion-hom-Subprecategory C P x y f))

  associative-composition-operation-Subprecategory :
    associative-composition-operation-binary-family-Set hom-set-Subprecategory
  pr1 associative-composition-operation-Subprecategory {x} {y} {z} =
    comp-hom-Subprecategory {x} {y} {z}
  pr1
    ( pr2
      associative-composition-operation-Subprecategory {x} {y} {z} {w} h g f) =
    associative-comp-hom-Subprecategory {x} {y} {z} {w} h g f
  pr2
    ( pr2
      associative-composition-operation-Subprecategory {x} {y} {z} {w} h g f) =
    inv-associative-comp-hom-Subprecategory {x} {y} {z} {w} h g f

  is-unital-composition-operation-Subprecategory :
    is-unital-composition-operation-binary-family-Set
      ( hom-set-Subprecategory)
      ( comp-hom-Subprecategory)
  pr1 is-unital-composition-operation-Subprecategory x =
    id-hom-Subprecategory {x}
  pr1 (pr2 is-unital-composition-operation-Subprecategory) {x} {y} =
    left-unit-law-comp-hom-Subprecategory {x} {y}
  pr2 (pr2 is-unital-composition-operation-Subprecategory) {x} {y} =
    right-unit-law-comp-hom-Subprecategory {x} {y}

  precategory-Subprecategory : Precategory (l1 ⊔ l3) (l2 ⊔ l4)
  pr1 precategory-Subprecategory = obj-Subprecategory C P
  pr1 (pr2 precategory-Subprecategory) = hom-set-Subprecategory
  pr1 (pr2 (pr2 precategory-Subprecategory)) =
    associative-composition-operation-Subprecategory
  pr2 (pr2 (pr2 precategory-Subprecategory)) =
    is-unital-composition-operation-Subprecategory
```

### The inclusion functor of a subprecategory

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2)
  (P : Subprecategory l3 l4 C)
  where

  inclusion-map-Subprecategory :
    map-Precategory (precategory-Subprecategory C P) C
  pr1 inclusion-map-Subprecategory =
    inclusion-obj-Subprecategory C P
  pr2 inclusion-map-Subprecategory {x} {y} =
    inclusion-hom-Subprecategory C P x y

  is-functor-inclusion-Subprecategory :
    is-functor-map-Precategory
      ( precategory-Subprecategory C P)
      ( C)
      ( inclusion-map-Subprecategory)
  pr1 is-functor-inclusion-Subprecategory g f = refl
  pr2 is-functor-inclusion-Subprecategory x = refl

  inclusion-Subprecategory :
    functor-Precategory (precategory-Subprecategory C P) C
  pr1 inclusion-Subprecategory =
    inclusion-obj-Subprecategory C P
  pr1 (pr2 inclusion-Subprecategory) {x} {y} =
    inclusion-hom-Subprecategory C P x y
  pr2 (pr2 inclusion-Subprecategory) =
    is-functor-inclusion-Subprecategory
```

## Properties

### The inclusion functor is an embedding on objects and hom-sets

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2)
  (P : Subprecategory l3 l4 C)
  where

  is-faithful-inclusion-Subprecategory :
    is-faithful-functor-Precategory
      ( precategory-Subprecategory C P)
      ( C)
      ( inclusion-Subprecategory C P)
  is-faithful-inclusion-Subprecategory x y =
    is-emb-inclusion-subtype
      ( subtype-hom-Subprecategory C P
        ( inclusion-obj-Subprecategory C P x)
        ( inclusion-obj-Subprecategory C P y)
        ( is-in-obj-inclusion-obj-Subprecategory C P x)
        ( is-in-obj-inclusion-obj-Subprecategory C P y))

  is-emb-obj-inclusion-Subprecategory :
    is-emb
      ( obj-functor-Precategory
        ( precategory-Subprecategory C P)
        ( C)
        ( inclusion-Subprecategory C P))
  is-emb-obj-inclusion-Subprecategory =
    is-emb-inclusion-subtype (subtype-obj-Subprecategory C P)
```

## See also

- [Large subprecategories](category-theory.large-subprecategories.md)
- [Subcategories](category-theory.subcategories.md)

## External links

- [subcategory](https://ncatlab.org/nlab/show/subcategory) at $n$Lab
- [Subcategory](https://en.wikipedia.org/wiki/Subcategory) at Wikipedia
- [Subcategory](https://mathworld.wolfram.com/Subcategory.html) at Wolfram
  MathWorld
