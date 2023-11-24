# Natural isomorphisms between maps between categories

```agda
module category-theory.natural-isomorphisms-maps-categories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.categories
open import category-theory.isomorphisms-in-categories
open import category-theory.maps-categories
open import category-theory.natural-isomorphisms-maps-precategories
open import category-theory.natural-transformations-maps-categories

open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.subtypes
open import foundation.universe-levels
```

</details>

## Idea

A **natural isomorphism** `γ` from [map](category-theory.maps-categories.md)
`F : C → D` to `G : C → D` is a
[natural transformation](category-theory.natural-transformations-maps-categories.md)
from `F` to `G` such that the morphism `γ F : hom (F x) (G x)` is an
[isomorphism](category-theory.isomorphisms-in-categories.md), for every object
`x` in `C`.

## Definition

### Families of isomorphisms between maps

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Category l1 l2)
  (D : Category l3 l4)
  (F G : map-Category C D)
  where

  iso-family-map-Category : UU (l1 ⊔ l4)
  iso-family-map-Category =
    iso-family-map-Precategory
      ( precategory-Category C)
      ( precategory-Category D)
      ( F)
      ( G)
```

### The predicate of being an isomorphism in a category

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Category l1 l2)
  (D : Category l3 l4)
  (F G : map-Category C D)
  where

  is-natural-isomorphism-map-Category :
    natural-transformation-map-Category C D F G → UU (l1 ⊔ l4)
  is-natural-isomorphism-map-Category =
    is-natural-isomorphism-map-Precategory
      ( precategory-Category C)
      ( precategory-Category D)
      ( F)
      ( G)

module _
  {l1 l2 l3 l4 : Level}
  (C : Category l1 l2)
  (D : Category l3 l4)
  (F G : map-Category C D)
  (f : natural-transformation-map-Category C D F G)
  where

  hom-inv-family-is-natural-isomorphism-map-Category :
    is-natural-isomorphism-map-Category C D F G f →
    hom-family-map-Category C D G F
  hom-inv-family-is-natural-isomorphism-map-Category =
    hom-inv-family-is-natural-isomorphism-map-Precategory
      ( precategory-Category C)
      ( precategory-Category D)
      ( F)
      ( G)
      ( f)

  is-section-hom-inv-family-is-natural-isomorphism-map-Category :
    (is-iso-f : is-natural-isomorphism-map-Category C D F G f) →
    (x : obj-Category C) →
    comp-hom-Category D
      ( hom-family-natural-transformation-map-Category C D F G f x)
      ( hom-inv-is-iso-Category D (is-iso-f x)) ＝
    id-hom-Category D
  is-section-hom-inv-family-is-natural-isomorphism-map-Category =
    is-section-hom-inv-family-is-natural-isomorphism-map-Precategory
      ( precategory-Category C)
      ( precategory-Category D)
      ( F)
      ( G)
      ( f)

  is-retraction-hom-inv-family-is-natural-isomorphism-map-Category :
    (is-iso-f : is-natural-isomorphism-map-Category C D F G f) →
    (x : obj-Category C) →
    comp-hom-Category D
      ( hom-inv-is-iso-Category D (is-iso-f x))
      ( hom-family-natural-transformation-map-Category C D F G f x) ＝
    id-hom-Category D
  is-retraction-hom-inv-family-is-natural-isomorphism-map-Category =
    is-retraction-hom-inv-family-is-natural-isomorphism-map-Precategory
      ( precategory-Category C)
      ( precategory-Category D)
      ( F)
      ( G)
      ( f)

  iso-family-is-natural-isomorphism-map-Category :
    is-natural-isomorphism-map-Category C D F G f →
    iso-family-map-Category C D F G
  iso-family-is-natural-isomorphism-map-Category =
    iso-family-is-natural-isomorphism-map-Precategory
      ( precategory-Category C)
      ( precategory-Category D)
      ( F)
      ( G)
      ( f)

  inv-iso-family-is-natural-isomorphism-map-Category :
    is-natural-isomorphism-map-Category C D F G f →
    iso-family-map-Category C D G F
  inv-iso-family-is-natural-isomorphism-map-Category =
    inv-iso-family-is-natural-isomorphism-map-Precategory
      ( precategory-Category C)
      ( precategory-Category D)
      ( F)
      ( G)
      ( f)
```

### Natural isomorphisms in a category

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Category l1 l2)
  (D : Category l3 l4)
  (F G : map-Category C D)
  where

  natural-isomorphism-map-Category : UU (l1 ⊔ l2 ⊔ l4)
  natural-isomorphism-map-Category =
    natural-isomorphism-map-Precategory
      ( precategory-Category C)
      ( precategory-Category D)
      ( F)
      ( G)

module _
  {l1 l2 l3 l4 : Level}
  (C : Category l1 l2)
  (D : Category l3 l4)
  (F G : map-Category C D)
  (f : natural-isomorphism-map-Category C D F G)
  where

  natural-transformation-map-natural-isomorphism-map-Category :
    natural-transformation-map-Category C D F G
  natural-transformation-map-natural-isomorphism-map-Category =
    natural-transformation-map-natural-isomorphism-map-Precategory
      ( precategory-Category C)
      ( precategory-Category D)
      ( F)
      ( G)
      ( f)

  hom-family-natural-isomorphism-map-Category :
    hom-family-map-Category C D F G
  hom-family-natural-isomorphism-map-Category =
    hom-family-natural-transformation-map-Category C D F G
      ( natural-transformation-map-natural-isomorphism-map-Category)

  coherence-square-natural-isomorphism-map-Category :
    is-natural-transformation-map-Category C D F G
      ( hom-family-natural-transformation-map-Category C D F G
        ( natural-transformation-map-natural-isomorphism-map-Category))
  coherence-square-natural-isomorphism-map-Category =
    naturality-natural-transformation-map-Category C D F G
      ( natural-transformation-map-natural-isomorphism-map-Category)

  is-natural-isomorphism-map-natural-isomorphism-map-Category :
    is-natural-isomorphism-map-Category C D F G
      ( natural-transformation-map-natural-isomorphism-map-Category)
  is-natural-isomorphism-map-natural-isomorphism-map-Category = pr2 f

  hom-inv-family-natural-isomorphism-map-Category :
    hom-family-map-Category C D G F
  hom-inv-family-natural-isomorphism-map-Category =
    hom-inv-family-is-natural-isomorphism-map-Category C D F G
      ( natural-transformation-map-natural-isomorphism-map-Category)
      ( is-natural-isomorphism-map-natural-isomorphism-map-Category)

  is-section-hom-inv-family-natural-isomorphism-map-Category :
    (x : obj-Category C) →
    comp-hom-Category D
      ( hom-family-natural-isomorphism-map-Category x)
      ( hom-inv-family-natural-isomorphism-map-Category x) ＝
    id-hom-Category D
  is-section-hom-inv-family-natural-isomorphism-map-Category =
    is-section-hom-inv-family-is-natural-isomorphism-map-Category C D F G
      ( natural-transformation-map-natural-isomorphism-map-Category)
      ( is-natural-isomorphism-map-natural-isomorphism-map-Category)

  is-retraction-hom-inv-family-natural-isomorphism-map-Category :
    (x : obj-Category C) →
    comp-hom-Category D
      ( hom-inv-family-natural-isomorphism-map-Category x)
      ( hom-family-natural-isomorphism-map-Category x) ＝
    id-hom-Category D
  is-retraction-hom-inv-family-natural-isomorphism-map-Category =
    is-retraction-hom-inv-family-is-natural-isomorphism-map-Category C D F G
      ( natural-transformation-map-natural-isomorphism-map-Category)
      ( is-natural-isomorphism-map-natural-isomorphism-map-Category)

  iso-family-natural-isomorphism-map-Category :
    iso-family-map-Category C D F G
  iso-family-natural-isomorphism-map-Category =
    iso-family-is-natural-isomorphism-map-Category C D F G
      ( natural-transformation-map-natural-isomorphism-map-Category)
      ( is-natural-isomorphism-map-natural-isomorphism-map-Category)

  inv-iso-family-natural-isomorphism-map-Category :
    iso-family-map-Category C D G F
  inv-iso-family-natural-isomorphism-map-Category =
    inv-iso-family-is-natural-isomorphism-map-Category C D F G
      ( natural-transformation-map-natural-isomorphism-map-Category)
      ( is-natural-isomorphism-map-natural-isomorphism-map-Category)
```

## Examples

### The identity natural isomorphism

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Category l1 l2)
  (D : Category l3 l4)
  where

  id-natural-isomorphism-map-Category :
    (F : map-Category C D) → natural-isomorphism-map-Category C D F F
  id-natural-isomorphism-map-Category =
    id-natural-isomorphism-map-Precategory
      ( precategory-Category C)
      ( precategory-Category D)
```

### Equalities induce natural isomorphisms

An equality between maps `F` and `G` gives rise to a natural isomorphism between
them. This is because, by the J-rule, it is enough to construct a natural
isomorphism given `refl : F ＝ F`, from `F` to itself. We take the identity
natural transformation as such an isomorphism.

```agda
natural-isomorphism-map-eq-Category :
  {l1 l2 l3 l4 : Level}
  (C : Category l1 l2)
  (D : Category l3 l4)
  (F G : map-Category C D) →
  F ＝ G → natural-isomorphism-map-Category C D F G
natural-isomorphism-map-eq-Category C D F .F refl =
  id-natural-isomorphism-map-Category C D F
```

## Propositions

### Being a natural isomorphism is a proposition

That a natural transformation is a natural isomorphism is a proposition. This
follows from the fact that being an isomorphism is a proposition.

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Category l1 l2)
  (D : Category l3 l4)
  (F G : map-Category C D)
  where

  is-prop-is-natural-isomorphism-map-Category :
    (f : natural-transformation-map-Category C D F G) →
    is-prop (is-natural-isomorphism-map-Category C D F G f)
  is-prop-is-natural-isomorphism-map-Category =
    is-prop-is-natural-isomorphism-map-Precategory
      ( precategory-Category C)
      ( precategory-Category D)
      ( F)
      ( G)

  is-natural-isomorphism-map-prop-hom-Category :
    (f : natural-transformation-map-Category C D F G) → Prop (l1 ⊔ l4)
  is-natural-isomorphism-map-prop-hom-Category =
    is-natural-isomorphism-map-prop-hom-Precategory
      ( precategory-Category C)
      ( precategory-Category D)
      ( F)
      ( G)
```

### Equality of natural isomorphisms is equality of their underlying natural transformations

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Category l1 l2)
  (D : Category l3 l4)
  (F G : map-Category C D)
  where

  extensionality-natural-isomorphism-map-Category :
    (f g : natural-isomorphism-map-Category C D F G) →
    (f ＝ g) ≃
    ( hom-family-natural-isomorphism-map-Category C D F G f ~
      hom-family-natural-isomorphism-map-Category C D F G g)
  extensionality-natural-isomorphism-map-Category =
    extensionality-natural-isomorphism-map-Precategory
      ( precategory-Category C)
      ( precategory-Category D)
      ( F)
      ( G)

  eq-eq-natural-transformation-map-natural-isomorphism-map-Category :
    (f g : natural-isomorphism-map-Category C D F G) →
    ( natural-transformation-map-natural-isomorphism-map-Category C D F G f ＝
      natural-transformation-map-natural-isomorphism-map-Category C D F G g) →
    f ＝ g
  eq-eq-natural-transformation-map-natural-isomorphism-map-Category f g =
    eq-type-subtype (is-natural-isomorphism-map-prop-hom-Category C D F G)

  eq-htpy-hom-family-natural-isomorphism-map-Category :
        (f g : natural-isomorphism-map-Category C D F G) →
    ( hom-family-natural-isomorphism-map-Category C D F G f ~
      hom-family-natural-isomorphism-map-Category C D F G g) →
    f ＝ g
  eq-htpy-hom-family-natural-isomorphism-map-Category =
    eq-htpy-hom-family-natural-isomorphism-map-Precategory
      ( precategory-Category C)
      ( precategory-Category D)
      ( F)
      ( G)
```

### The type of natural isomorphisms form a set

The type of natural isomorphisms between maps `F` and `G` is a
[subtype](foundation-core.subtypes.md) of the [set](foundation-core.sets.md)
`natural-transformation F G` since being an isomorphism is a proposition.

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Category l1 l2)
  (D : Category l3 l4)
  (F G : map-Category C D)
  where

  is-set-natural-isomorphism-map-Category :
    is-set (natural-isomorphism-map-Category C D F G)
  is-set-natural-isomorphism-map-Category =
    is-set-type-subtype
      ( is-natural-isomorphism-map-prop-hom-Category C D F G)
      ( is-set-natural-transformation-map-Category C D F G)

  natural-isomorphism-map-set-Category : Set (l1 ⊔ l2 ⊔ l4)
  pr1 natural-isomorphism-map-set-Category =
    natural-isomorphism-map-Category C D F G
  pr2 natural-isomorphism-map-set-Category =
    is-set-natural-isomorphism-map-Category
```

### Inverses of natural isomorphisms are natural isomorphisms

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Category l1 l2)
  (D : Category l3 l4)
  (F G : map-Category C D)
  (f : natural-transformation-map-Category C D F G)
  where

  natural-transformation-map-inv-is-natural-isomorphism-map-Category :
    is-natural-isomorphism-map-Category C D F G f →
    natural-transformation-map-Category C D G F
  natural-transformation-map-inv-is-natural-isomorphism-map-Category =
    natural-transformation-map-inv-is-natural-isomorphism-map-Precategory
      ( precategory-Category C)
      ( precategory-Category D)
      ( F)
      ( G)
      ( f)

  is-section-natural-transformation-map-inv-is-natural-isomorphism-map-Category :
    (is-iso-f : is-natural-isomorphism-map-Category C D F G f) →
    comp-natural-transformation-map-Category C D G F G
      ( f)
      ( natural-transformation-map-inv-is-natural-isomorphism-map-Category
        ( is-iso-f)) ＝
    id-natural-transformation-map-Category C D G
  is-section-natural-transformation-map-inv-is-natural-isomorphism-map-Category
    is-iso-f =
    eq-htpy-hom-family-natural-transformation-map-Category C D G G _ _
      ( is-section-hom-inv-is-iso-Category D ∘ is-iso-f)

  is-retraction-natural-transformation-map-inv-is-natural-isomorphism-map-Category :
    (is-iso-f : is-natural-isomorphism-map-Category C D F G f) →
    comp-natural-transformation-map-Category C D F G F
      ( natural-transformation-map-inv-is-natural-isomorphism-map-Category
        ( is-iso-f))
      ( f) ＝
    id-natural-transformation-map-Category C D F
  is-retraction-natural-transformation-map-inv-is-natural-isomorphism-map-Category
    is-iso-f =
    eq-htpy-hom-family-natural-transformation-map-Category C D F F _ _
      ( is-retraction-hom-inv-is-iso-Category D ∘ is-iso-f)

  is-natural-isomorphism-map-inv-is-natural-isomorphism-map-Category :
    (is-iso-f : is-natural-isomorphism-map-Category C D F G f) →
    is-natural-isomorphism-map-Category C D G F
      ( natural-transformation-map-inv-is-natural-isomorphism-map-Category
        ( is-iso-f))
  is-natural-isomorphism-map-inv-is-natural-isomorphism-map-Category is-iso-f =
    is-iso-inv-is-iso-Category D ∘ is-iso-f
```

### Inverses of natural isomorphisms

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Category l1 l2)
  (D : Category l3 l4)
  (F G : map-Category C D)
  (f : natural-isomorphism-map-Category C D F G)
  where

  natural-transformation-map-inv-natural-isomorphism-map-Category :
    natural-transformation-map-Category C D G F
  natural-transformation-map-inv-natural-isomorphism-map-Category =
    natural-transformation-map-inv-is-natural-isomorphism-map-Category C D F G
      ( natural-transformation-map-natural-isomorphism-map-Category C D F G f)
      ( is-natural-isomorphism-map-natural-isomorphism-map-Category C D F G f)

  is-section-natural-transformation-map-inv-natural-isomorphism-map-Category :
    ( comp-natural-transformation-map-Category C D G F G
      ( natural-transformation-map-natural-isomorphism-map-Category C D F G f)
      ( natural-transformation-map-inv-natural-isomorphism-map-Category)) ＝
    ( id-natural-transformation-map-Category C D G)
  is-section-natural-transformation-map-inv-natural-isomorphism-map-Category =
    is-section-natural-transformation-map-inv-is-natural-isomorphism-map-Category
      C D F G
      ( natural-transformation-map-natural-isomorphism-map-Category C D F G f)
      ( is-natural-isomorphism-map-natural-isomorphism-map-Category C D F G f)

  is-retraction-natural-transformation-map-inv-natural-isomorphism-map-Category :
    ( comp-natural-transformation-map-Category C D F G F
      ( natural-transformation-map-inv-natural-isomorphism-map-Category)
      ( natural-transformation-map-natural-isomorphism-map-Category
          C D F G f)) ＝
    ( id-natural-transformation-map-Category C D F)
  is-retraction-natural-transformation-map-inv-natural-isomorphism-map-Category =
    is-retraction-natural-transformation-map-inv-is-natural-isomorphism-map-Category
      C D F G
      ( natural-transformation-map-natural-isomorphism-map-Category C D F G f)
      ( is-natural-isomorphism-map-natural-isomorphism-map-Category C D F G f)

  is-natural-isomorphism-map-inv-natural-isomorphism-map-Category :
    is-natural-isomorphism-map-Category C D G F
      ( natural-transformation-map-inv-natural-isomorphism-map-Category)
  is-natural-isomorphism-map-inv-natural-isomorphism-map-Category =
    is-natural-isomorphism-map-inv-is-natural-isomorphism-map-Category C D F G
      ( natural-transformation-map-natural-isomorphism-map-Category C D F G f)
      ( is-natural-isomorphism-map-natural-isomorphism-map-Category C D F G f)

  inv-natural-isomorphism-map-Category :
    natural-isomorphism-map-Category C D G F
  pr1 inv-natural-isomorphism-map-Category =
    natural-transformation-map-inv-natural-isomorphism-map-Category
  pr2 inv-natural-isomorphism-map-Category =
    is-natural-isomorphism-map-inv-natural-isomorphism-map-Category
```

### Natural isomorphisms are closed under composition

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Category l1 l2)
  (D : Category l3 l4)
  (F G H : map-Category C D)
  (g : natural-transformation-map-Category C D G H)
  (f : natural-transformation-map-Category C D F G)
  where

  is-natural-isomorphism-map-comp-is-natural-isomorphism-map-Category :
    is-natural-isomorphism-map-Category C D G H g →
    is-natural-isomorphism-map-Category C D F G f →
    is-natural-isomorphism-map-Category C D F H
      ( comp-natural-transformation-map-Category C D F G H g f)
  is-natural-isomorphism-map-comp-is-natural-isomorphism-map-Category
    is-iso-g is-iso-f x =
      is-iso-comp-is-iso-Category D (is-iso-g x) (is-iso-f x)
```

### The composition operation on natural isomorphisms

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Category l1 l2)
  (D : Category l3 l4)
  (F G H : map-Category C D)
  (g : natural-isomorphism-map-Category C D G H)
  (f : natural-isomorphism-map-Category C D F G)
  where

  hom-comp-natural-isomorphism-map-Category :
    natural-transformation-map-Category C D F H
  hom-comp-natural-isomorphism-map-Category =
    comp-natural-transformation-map-Category C D F G H
      ( natural-transformation-map-natural-isomorphism-map-Category C D G H g)
      ( natural-transformation-map-natural-isomorphism-map-Category C D F G f)

  is-natural-isomorphism-map-comp-natural-isomorphism-map-Category :
    is-natural-isomorphism-map-Category C D F H
      ( hom-comp-natural-isomorphism-map-Category)
  is-natural-isomorphism-map-comp-natural-isomorphism-map-Category =
    is-natural-isomorphism-map-comp-is-natural-isomorphism-map-Category
      C D F G H
      ( natural-transformation-map-natural-isomorphism-map-Category C D G H g)
      ( natural-transformation-map-natural-isomorphism-map-Category C D F G f)
      ( is-natural-isomorphism-map-natural-isomorphism-map-Category C D G H g)
      ( is-natural-isomorphism-map-natural-isomorphism-map-Category C D F G f)

  comp-natural-isomorphism-map-Category :
    natural-isomorphism-map-Category C D F H
  pr1 comp-natural-isomorphism-map-Category =
    hom-comp-natural-isomorphism-map-Category
  pr2 comp-natural-isomorphism-map-Category =
    is-natural-isomorphism-map-comp-natural-isomorphism-map-Category

  natural-transformation-map-inv-comp-natural-isomorphism-map-Category :
    natural-transformation-map-Category C D H F
  natural-transformation-map-inv-comp-natural-isomorphism-map-Category =
    natural-transformation-map-inv-natural-isomorphism-map-Category C D F H
      ( comp-natural-isomorphism-map-Category)

  is-section-inv-comp-natural-isomorphism-map-Category :
    ( comp-natural-transformation-map-Category C D H F H
      ( hom-comp-natural-isomorphism-map-Category)
      ( natural-transformation-map-inv-comp-natural-isomorphism-map-Category)) ＝
    ( id-natural-transformation-map-Category C D H)
  is-section-inv-comp-natural-isomorphism-map-Category =
    is-section-natural-transformation-map-inv-natural-isomorphism-map-Category
      C D F H comp-natural-isomorphism-map-Category

  is-retraction-inv-comp-natural-isomorphism-map-Category :
    ( comp-natural-transformation-map-Category C D F H F
      ( natural-transformation-map-inv-comp-natural-isomorphism-map-Category)
      ( hom-comp-natural-isomorphism-map-Category)) ＝
    ( id-natural-transformation-map-Category C D F)
  is-retraction-inv-comp-natural-isomorphism-map-Category =
    is-retraction-natural-transformation-map-inv-natural-isomorphism-map-Category
      C D F H comp-natural-isomorphism-map-Category
```

### Groupoid laws of natural isomorphisms in categories

#### Composition of natural isomorphisms satisfies the unit laws

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Category l1 l2)
  (D : Category l3 l4)
  (F G : map-Category C D)
  (f : natural-isomorphism-map-Category C D F G)
  where

  left-unit-law-comp-natural-isomorphism-map-Category :
    comp-natural-isomorphism-map-Category C D F G G
      ( id-natural-isomorphism-map-Category C D G)
      ( f) ＝
    f
  left-unit-law-comp-natural-isomorphism-map-Category =
    left-unit-law-comp-natural-isomorphism-map-Precategory
      ( precategory-Category C)
      ( precategory-Category D)
      ( F)
      ( G)
      ( f)

  right-unit-law-comp-natural-isomorphism-map-Category :
    comp-natural-isomorphism-map-Category C D F F G f
      ( id-natural-isomorphism-map-Category C D F) ＝
    f
  right-unit-law-comp-natural-isomorphism-map-Category =
    right-unit-law-comp-natural-isomorphism-map-Precategory
      ( precategory-Category C)
      ( precategory-Category D)
      ( F)
      ( G)
      ( f)
```

#### Composition of natural isomorphisms is associative

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Category l1 l2)
  (D : Category l3 l4)
  (F G H I : map-Category C D)
  (f : natural-isomorphism-map-Category C D F G)
  (g : natural-isomorphism-map-Category C D G H)
  (h : natural-isomorphism-map-Category C D H I)
  where

  associative-comp-natural-isomorphism-map-Category :
    ( comp-natural-isomorphism-map-Category C D F G I
      ( comp-natural-isomorphism-map-Category C D G H I h g)
      ( f)) ＝
    ( comp-natural-isomorphism-map-Category C D F H I h
      ( comp-natural-isomorphism-map-Category C D F G H g f))
  associative-comp-natural-isomorphism-map-Category =
    associative-comp-natural-isomorphism-map-Precategory
      ( precategory-Category C)
      ( precategory-Category D)
      ( F)
      ( G)
      ( H)
      ( I)
      ( f)
      ( g)
      ( h)
```

#### Composition of natural isomorphisms satisfies inverse laws

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Category l1 l2)
  (D : Category l3 l4)
  (F G : map-Category C D)
  (f : natural-isomorphism-map-Category C D F G)
  where

  left-inverse-law-comp-natural-isomorphism-map-Category :
    ( comp-natural-isomorphism-map-Category C D F G F
      ( inv-natural-isomorphism-map-Category C D F G f)
      ( f)) ＝
    ( id-natural-isomorphism-map-Category C D F)
  left-inverse-law-comp-natural-isomorphism-map-Category =
    left-inverse-law-comp-natural-isomorphism-map-Precategory
      ( precategory-Category C)
      ( precategory-Category D)
      ( F)
      ( G)
      ( f)

  right-inverse-law-comp-natural-isomorphism-map-Category :
    ( comp-natural-isomorphism-map-Category C D G F G
      ( f)
      ( inv-natural-isomorphism-map-Category C D F G f)) ＝
    ( id-natural-isomorphism-map-Category C D G)
  right-inverse-law-comp-natural-isomorphism-map-Category =
    right-inverse-law-comp-natural-isomorphism-map-Precategory
      ( precategory-Category C)
      ( precategory-Category D)
      ( F)
      ( G)
      ( f)
```

### When the type of natural transformations is a proposition, The type of natural isomorphisms is a proposition

The type of natural isomorphisms between maps `F` and `G` is a subtype of
`natural-transformation F G`, so when this type is a proposition, then the type
of natural isomorphisms from `F` to `G` form a proposition.

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Category l1 l2)
  (D : Category l3 l4)
  (F G : map-Category C D)
  where

  is-prop-natural-isomorphism-map-Category :
    is-prop (natural-transformation-map-Category C D F G) →
    is-prop (natural-isomorphism-map-Category C D F G)
  is-prop-natural-isomorphism-map-Category =
    is-prop-natural-isomorphism-map-Precategory
      ( precategory-Category C)
      ( precategory-Category D)
      ( F)
      ( G)

  natural-isomorphism-map-prop-Category :
    is-prop (natural-transformation-map-Category C D F G) → Prop (l1 ⊔ l2 ⊔ l4)
  natural-isomorphism-map-prop-Category =
    natural-isomorphism-map-prop-Precategory
      ( precategory-Category C)
      ( precategory-Category D)
      ( F)
      ( G)
```

### Functoriality of `natural-isomorphism-map-eq`

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Category l1 l2)
  (D : Category l3 l4)
  (F G H : map-Category C D)
  where

  preserves-concat-natural-isomorphism-map-eq-Category :
    (p : F ＝ G) (q : G ＝ H) →
    natural-isomorphism-map-eq-Category C D F H (p ∙ q) ＝
    comp-natural-isomorphism-map-Category C D F G H
      ( natural-isomorphism-map-eq-Category C D G H q)
      ( natural-isomorphism-map-eq-Category C D F G p)
  preserves-concat-natural-isomorphism-map-eq-Category refl q =
    inv
      ( right-unit-law-comp-natural-isomorphism-map-Category C D F H
        ( natural-isomorphism-map-eq-Category C D G H q))
```
