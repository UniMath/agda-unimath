# Functors between categories

```agda
module category-theory.functors-categories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.categories
open import category-theory.functors-precategories
open import category-theory.maps-categories

open import foundation.equivalences
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.propositions
open import foundation.universe-levels
```

</details>

## Idea

A **functor** between two [categories](category-theory.categories.md) is a
[functor](category-theory.functors-precategories.md) between the underlying
[precategories](category-theory.precategories.md).

## Definition

### The predicate of being a functor on maps between categories

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Category l1 l2)
  (D : Category l3 l4)
  (F : map-Category C D)
  where

  preserves-comp-map-Category : UU (l1 ⊔ l2 ⊔ l4)
  preserves-comp-map-Category =
    preserves-comp-map-Precategory
      ( precategory-Category C)
      ( precategory-Category D)
      ( F)

  preserves-id-map-Category : UU (l1 ⊔ l4)
  preserves-id-map-Category =
    preserves-id-map-Precategory
      ( precategory-Category C)
      ( precategory-Category D)
      ( F)

  is-functor-map-Category : UU (l1 ⊔ l2 ⊔ l4)
  is-functor-map-Category =
    is-functor-map-Precategory
      ( precategory-Category C)
      ( precategory-Category D)
      ( F)

  preserves-comp-is-functor-map-Category :
    is-functor-map-Category → preserves-comp-map-Category
  preserves-comp-is-functor-map-Category =
    preserves-comp-is-functor-map-Precategory
      ( precategory-Category C)
      ( precategory-Category D)
      ( F)

  preserves-id-hom-is-functor-map-Category :
    is-functor-map-Category → preserves-id-map-Category
  preserves-id-hom-is-functor-map-Category =
    preserves-id-hom-is-functor-map-Precategory
      ( precategory-Category C)
      ( precategory-Category D)
      ( F)
```

### functors between categories

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Category l1 l2)
  (D : Category l3 l4)
  where

  functor-Category : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  functor-Category =
    functor-Precategory (precategory-Category C) (precategory-Category D)

  obj-functor-Category : functor-Category → obj-Category C → obj-Category D
  obj-functor-Category =
    obj-functor-Precategory
      ( precategory-Category C)
      ( precategory-Category D)

  hom-functor-Category :
    (F : functor-Category) →
    {x y : obj-Category C} →
    (f : hom-Category C x y) →
    hom-Category D
      ( obj-functor-Category F x)
      ( obj-functor-Category F y)
  hom-functor-Category =
    hom-functor-Precategory
      ( precategory-Category C)
      ( precategory-Category D)

  map-functor-Category : functor-Category → map-Category C D
  map-functor-Category =
    map-functor-Precategory (precategory-Category C) (precategory-Category D)

  preserves-comp-functor-Category :
    ( F : functor-Category) {x y z : obj-Category C}
    ( g : hom-Category C y z) (f : hom-Category C x y) →
    ( hom-functor-Category F (comp-hom-Category C g f)) ＝
    ( comp-hom-Category D
      ( hom-functor-Category F g)
      ( hom-functor-Category F f))
  preserves-comp-functor-Category =
    preserves-comp-functor-Precategory
      ( precategory-Category C)
      ( precategory-Category D)

  preserves-id-functor-Category :
    (F : functor-Category) (x : obj-Category C) →
    hom-functor-Category F (id-hom-Category C {x}) ＝
    id-hom-Category D {obj-functor-Category F x}
  preserves-id-functor-Category =
    preserves-id-functor-Precategory
      ( precategory-Category C)
      ( precategory-Category D)
```

## Examples

### The identity functor

There is an identity functor on any category.

```agda
id-functor-Category :
  {l1 l2 : Level} (C : Category l1 l2) → functor-Category C C
id-functor-Category C = id-functor-Precategory (precategory-Category C)
```

### Composition of functors

Any two compatible functors can be composed to a new functor.

```agda
comp-functor-Category :
  {l1 l2 l3 l4 l5 l6 : Level}
  (C : Category l1 l2) (D : Category l3 l4) (E : Category l5 l6) →
  functor-Category D E → functor-Category C D → functor-Category C E
comp-functor-Category C D E =
  comp-functor-Precategory
    ( precategory-Category C)
    ( precategory-Category D)
    ( precategory-Category E)
```

## Properties

### Respecting identities and compositions are propositions

This follows from the fact that the hom-types are
[sets](foundation-core.sets.md).

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Category l1 l2)
  (D : Category l3 l4)
  (F : map-Category C D)
  where

  is-prop-preserves-comp-map-Category :
    is-prop (preserves-comp-map-Category C D F)
  is-prop-preserves-comp-map-Category =
    is-prop-preserves-comp-map-Precategory
      ( precategory-Category C)
      ( precategory-Category D)
      ( F)

  preserves-comp-hom-prop-map-Category : Prop (l1 ⊔ l2 ⊔ l4)
  preserves-comp-hom-prop-map-Category =
    preserves-comp-hom-prop-map-Precategory
      ( precategory-Category C)
      ( precategory-Category D)
      ( F)

  is-prop-preserves-id-map-Category :
    is-prop (preserves-id-map-Category C D F)
  is-prop-preserves-id-map-Category =
    is-prop-preserves-id-map-Precategory
      ( precategory-Category C)
      ( precategory-Category D)
      ( F)

  preserves-id-hom-prop-map-Category : Prop (l1 ⊔ l4)
  preserves-id-hom-prop-map-Category =
    preserves-id-hom-prop-map-Precategory
      ( precategory-Category C)
      ( precategory-Category D)
      ( F)

  is-prop-is-functor-map-Category :
    is-prop (is-functor-map-Category C D F)
  is-prop-is-functor-map-Category =
    is-prop-is-functor-map-Precategory
      ( precategory-Category C)
      ( precategory-Category D)
      ( F)

  is-functor-prop-map-Category : Prop (l1 ⊔ l2 ⊔ l4)
  is-functor-prop-map-Category =
    is-functor-prop-map-Precategory
      ( precategory-Category C)
      ( precategory-Category D)
      ( F)
```

### Extensionality of functors between categories

#### Equality of functors is equality of underlying maps

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Category l1 l2)
  (D : Category l3 l4)
  (F G : functor-Category C D)
  where

  equiv-eq-map-eq-functor-Category :
    (F ＝ G) ≃ (map-functor-Category C D F ＝ map-functor-Category C D G)
  equiv-eq-map-eq-functor-Category =
    equiv-eq-map-eq-functor-Precategory
      ( precategory-Category C)
      ( precategory-Category D)
      ( F)
      ( G)

  eq-map-eq-functor-Category :
    (F ＝ G) → (map-functor-Category C D F ＝ map-functor-Category C D G)
  eq-map-eq-functor-Category =
    map-equiv equiv-eq-map-eq-functor-Category

  eq-eq-map-functor-Category :
    (map-functor-Category C D F ＝ map-functor-Category C D G) → (F ＝ G)
  eq-eq-map-functor-Category =
    map-inv-equiv equiv-eq-map-eq-functor-Category

  is-section-eq-eq-map-functor-Category :
    eq-map-eq-functor-Category ∘ eq-eq-map-functor-Category ~ id
  is-section-eq-eq-map-functor-Category =
    is-section-map-inv-equiv equiv-eq-map-eq-functor-Category

  is-retraction-eq-eq-map-functor-Category :
    eq-eq-map-functor-Category ∘ eq-map-eq-functor-Category ~ id
  is-retraction-eq-eq-map-functor-Category =
    is-retraction-map-inv-equiv equiv-eq-map-eq-functor-Category
```

#### Equality of functors is homotopy of underlying maps

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Category l1 l2)
  (D : Category l3 l4)
  (F G : functor-Category C D)
  where

  equiv-htpy-map-eq-functor-Category :
    (F ＝ G) ≃
    ( htpy-map-Category C D
      ( map-functor-Category C D F)
      ( map-functor-Category C D G))
  equiv-htpy-map-eq-functor-Category =
    equiv-htpy-map-eq-functor-Precategory
      ( precategory-Category C)
      ( precategory-Category D)
      ( F)
      ( G)

  htpy-map-eq-functor-Category :
    (F ＝ G) →
    htpy-map-Category C D
      ( map-functor-Category C D F)
      ( map-functor-Category C D G)
  htpy-map-eq-functor-Category =
    map-equiv equiv-htpy-map-eq-functor-Category

  eq-htpy-map-functor-Category :
    htpy-map-Category C D
      ( map-functor-Category C D F)
      ( map-functor-Category C D G) →
    ( F ＝ G)
  eq-htpy-map-functor-Category =
    map-inv-equiv equiv-htpy-map-eq-functor-Category

  is-section-eq-htpy-map-functor-Category :
    htpy-map-eq-functor-Category ∘ eq-htpy-map-functor-Category ~ id
  is-section-eq-htpy-map-functor-Category =
    is-section-map-inv-equiv equiv-htpy-map-eq-functor-Category

  is-retraction-eq-htpy-map-functor-Category :
    eq-htpy-map-functor-Category ∘ htpy-map-eq-functor-Category ~ id
  is-retraction-eq-htpy-map-functor-Category =
    is-retraction-map-inv-equiv equiv-htpy-map-eq-functor-Category
```
