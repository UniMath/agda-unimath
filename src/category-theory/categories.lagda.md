# Categories

```agda
module category-theory.categories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.composition-operations-on-binary-families-of-sets
open import category-theory.isomorphisms-in-precategories
open import category-theory.nonunital-precategories
open import category-theory.precategories
open import category-theory.preunivalent-categories

open import foundation.1-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.universe-levels
```

</details>

## Idea

A **category** in Homotopy Type Theory is a
[precategory](category-theory.precategories.md) for which the
[identifications](foundation-core.identity-types.md) between the objects are the
[isomorphisms](category-theory.isomorphisms-in-precategories.md). More
specifically, an equality between objects gives rise to an isomorphism between
them, by the J-rule. A precategory is a category if this function, called
`iso-eq`, is an [equivalence](foundation-core.equivalences.md). In particular.
being a category is a [proposition](foundation-core.propositions.md) since
`is-equiv` is a proposition.

## Definitions

### The predicate of being a category on precategories

```agda
module _
  {l1 l2 : Level} (C : Precategory l1 l2)
  where

  is-category-prop-Precategory : Prop (l1 ⊔ l2)
  is-category-prop-Precategory =
    Π-Prop
      ( obj-Precategory C)
      ( λ x →
        Π-Prop
          ( obj-Precategory C)
          ( λ y → is-equiv-Prop (iso-eq-Precategory C x y)))

  is-category-Precategory : UU (l1 ⊔ l2)
  is-category-Precategory = type-Prop is-category-prop-Precategory
```

### The type of categories

```agda
Category : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
Category l1 l2 = Σ (Precategory l1 l2) is-category-Precategory

module _
  {l1 l2 : Level} (C : Category l1 l2)
  where

  precategory-Category : Precategory l1 l2
  precategory-Category = pr1 C

  obj-Category : UU l1
  obj-Category = obj-Precategory precategory-Category

  hom-set-Category : obj-Category → obj-Category → Set l2
  hom-set-Category = hom-set-Precategory precategory-Category

  hom-Category : obj-Category → obj-Category → UU l2
  hom-Category = hom-Precategory precategory-Category

  is-set-hom-Category :
    (x y : obj-Category) → is-set (hom-Category x y)
  is-set-hom-Category = is-set-hom-Precategory precategory-Category

  comp-hom-Category :
    {x y z : obj-Category} →
    hom-Category y z → hom-Category x y → hom-Category x z
  comp-hom-Category = comp-hom-Precategory precategory-Category

  associative-comp-hom-Category :
    {x y z w : obj-Category}
    (h : hom-Category z w)
    (g : hom-Category y z)
    (f : hom-Category x y) →
    comp-hom-Category (comp-hom-Category h g) f ＝
    comp-hom-Category h (comp-hom-Category g f)
  associative-comp-hom-Category =
    associative-comp-hom-Precategory precategory-Category

  associative-composition-operation-Category :
    associative-composition-operation-binary-family-Set hom-set-Category
  associative-composition-operation-Category =
    associative-composition-operation-Precategory precategory-Category

  id-hom-Category : {x : obj-Category} → hom-Category x x
  id-hom-Category = id-hom-Precategory precategory-Category

  left-unit-law-comp-hom-Category :
    {x y : obj-Category} (f : hom-Category x y) →
    comp-hom-Category id-hom-Category f ＝ f
  left-unit-law-comp-hom-Category =
    left-unit-law-comp-hom-Precategory precategory-Category

  right-unit-law-comp-hom-Category :
    {x y : obj-Category} (f : hom-Category x y) →
    comp-hom-Category f id-hom-Category ＝ f
  right-unit-law-comp-hom-Category =
    right-unit-law-comp-hom-Precategory precategory-Category

  is-unital-composition-operation-Category :
    is-unital-composition-operation-binary-family-Set
      hom-set-Category
      comp-hom-Category
  is-unital-composition-operation-Category =
    is-unital-composition-operation-Precategory precategory-Category

  is-category-Category :
    is-category-Precategory precategory-Category
  is-category-Category = pr2 C
```

### The underlying nonunital precategory of a category

```agda
module _
  {l1 l2 : Level} (C : Category l1 l2)
  where

  nonunital-precategory-Category : Nonunital-Precategory l1 l2
  nonunital-precategory-Category =
    nonunital-precategory-Precategory (precategory-Category C)
```

### The underlying preunivalent category of a category

```agda
module _
  {l1 l2 : Level} (C : Category l1 l2)
  where

  preunivalent-category-Category : Preunivalent-Category l1 l2
  pr1 preunivalent-category-Category = precategory-Category C
  pr2 preunivalent-category-Category x y =
    is-emb-is-equiv (is-category-Category C x y)
```

### Precomposition by a morphism

```agda
precomp-hom-Category :
  {l1 l2 : Level} (C : Category l1 l2) {x y : obj-Category C}
  (f : hom-Category C x y) (z : obj-Category C) →
  hom-Category C y z → hom-Category C x z
precomp-hom-Category C = precomp-hom-Precategory (precategory-Category C)
```

### Postcomposition by a morphism

```agda
postcomp-hom-Category :
  {l1 l2 : Level} (C : Category l1 l2) {x y : obj-Category C}
  (f : hom-Category C x y) (z : obj-Category C) →
  hom-Category C z x → hom-Category C z y
postcomp-hom-Category C = postcomp-hom-Precategory (precategory-Category C)
```

### Equalities induce morphisms

```agda
module _
  {l1 l2 : Level} (C : Category l1 l2)
  where

  hom-eq-Category :
    (x y : obj-Category C) → x ＝ y → hom-Category C x y
  hom-eq-Category = hom-eq-Precategory (precategory-Category C)

  hom-inv-eq-Category :
    (x y : obj-Category C) → x ＝ y → hom-Category C y x
  hom-inv-eq-Category = hom-inv-eq-Precategory (precategory-Category C)
```

## Properties

### The objects in a category form a 1-type

The type of identities between two objects in a category is equivalent to the
type of isomorphisms between them. But this type is a set, and thus the identity
type is a set.

```agda
module _
  {l1 l2 : Level} (C : Category l1 l2)
  where

  is-1-type-obj-Category : is-1-type (obj-Category C)
  is-1-type-obj-Category =
    is-1-type-obj-Preunivalent-Category (preunivalent-category-Category C)

  obj-1-type-Category : 1-Type l1
  obj-1-type-Category =
    obj-1-type-Preunivalent-Category (preunivalent-category-Category C)
```
