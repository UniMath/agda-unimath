# Strict categories

```agda
module category-theory.strict-categories where
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
open import foundation.injective-maps
open import foundation.propositions
open import foundation.sets
open import foundation.subtypes
open import foundation.universe-levels
```

</details>

## Idea

A **strict category** in Homotopy Type Theory is a
[precategory](category-theory.precategories.md) for which the type of objects
form a [set](foundation-core.sets.md). In particular, being a strict category is
a [proposition](foundation-core.propositions.md) since being a set is a
proposition.

## Definitions

### The predicate on precategories of being a strict category

```agda
module _
  {l1 l2 : Level} (C : Precategory l1 l2)
  where

  is-strict-category-prop-Precategory : Prop l1
  is-strict-category-prop-Precategory =
    is-set-Prop (obj-Precategory C)

  is-strict-category-Precategory : UU l1
  is-strict-category-Precategory = type-Prop is-strict-category-prop-Precategory
```

### The type of strict categories

```agda
Strict-Category : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
Strict-Category l1 l2 = Σ (Precategory l1 l2) is-strict-category-Precategory

module _
  {l1 l2 : Level} (C : Strict-Category l1 l2)
  where

  precategory-Strict-Category : Precategory l1 l2
  precategory-Strict-Category = pr1 C

  obj-Strict-Category : UU l1
  obj-Strict-Category = obj-Precategory precategory-Strict-Category

  is-set-obj-Strict-Category : is-set obj-Strict-Category
  is-set-obj-Strict-Category = pr2 C

  hom-set-Strict-Category : obj-Strict-Category → obj-Strict-Category → Set l2
  hom-set-Strict-Category = hom-set-Precategory precategory-Strict-Category

  hom-Strict-Category : obj-Strict-Category → obj-Strict-Category → UU l2
  hom-Strict-Category = hom-Precategory precategory-Strict-Category

  is-set-hom-Strict-Category :
    (x y : obj-Strict-Category) → is-set (hom-Strict-Category x y)
  is-set-hom-Strict-Category =
    is-set-hom-Precategory precategory-Strict-Category

  comp-hom-Strict-Category :
    {x y z : obj-Strict-Category} →
    hom-Strict-Category y z → hom-Strict-Category x y → hom-Strict-Category x z
  comp-hom-Strict-Category = comp-hom-Precategory precategory-Strict-Category

  associative-comp-hom-Strict-Category :
    {x y z w : obj-Strict-Category}
    (h : hom-Strict-Category z w)
    (g : hom-Strict-Category y z)
    (f : hom-Strict-Category x y) →
    comp-hom-Strict-Category (comp-hom-Strict-Category h g) f ＝
    comp-hom-Strict-Category h (comp-hom-Strict-Category g f)
  associative-comp-hom-Strict-Category =
    associative-comp-hom-Precategory precategory-Strict-Category

  associative-composition-operation-Strict-Category :
    associative-composition-operation-binary-family-Set hom-set-Strict-Category
  associative-composition-operation-Strict-Category =
    associative-composition-operation-Precategory precategory-Strict-Category

  id-hom-Strict-Category : {x : obj-Strict-Category} → hom-Strict-Category x x
  id-hom-Strict-Category = id-hom-Precategory precategory-Strict-Category

  left-unit-law-comp-hom-Strict-Category :
    {x y : obj-Strict-Category} (f : hom-Strict-Category x y) →
    comp-hom-Strict-Category id-hom-Strict-Category f ＝ f
  left-unit-law-comp-hom-Strict-Category =
    left-unit-law-comp-hom-Precategory precategory-Strict-Category

  right-unit-law-comp-hom-Strict-Category :
    {x y : obj-Strict-Category} (f : hom-Strict-Category x y) →
    comp-hom-Strict-Category f id-hom-Strict-Category ＝ f
  right-unit-law-comp-hom-Strict-Category =
    right-unit-law-comp-hom-Precategory precategory-Strict-Category

  is-unital-composition-operation-Strict-Category :
    is-unital-composition-operation-binary-family-Set
      hom-set-Strict-Category
      comp-hom-Strict-Category
  is-unital-composition-operation-Strict-Category =
    is-unital-composition-operation-Precategory precategory-Strict-Category

  is-strict-category-Strict-Category :
    is-strict-category-Precategory precategory-Strict-Category
  is-strict-category-Strict-Category = pr2 C
```

### The underlying nonunital precategory of a strict category

```agda
module _
  {l1 l2 : Level} (C : Strict-Category l1 l2)
  where

  nonunital-precategory-Strict-Category : Nonunital-Precategory l1 l2
  nonunital-precategory-Strict-Category =
    nonunital-precategory-Precategory (precategory-Strict-Category C)
```

### The underlying preunivalent category of a strict category

```agda
module _
  {l1 l2 : Level} (C : Strict-Category l1 l2)
  where

  abstract
    is-preunivalent-Strict-Category :
      is-preunivalent-Precategory (precategory-Strict-Category C)
    is-preunivalent-Strict-Category x y =
      is-emb-is-injective
        ( is-set-type-subtype
          ( is-iso-prop-Precategory (precategory-Strict-Category C))
          ( is-set-hom-Strict-Category C x y))
        ( λ where
          {refl} {q} _ →
            axiom-K-is-set (is-set-obj-Strict-Category C) x q)

  preunivalent-category-Strict-Category : Preunivalent-Category l1 l2
  pr1 preunivalent-category-Strict-Category = precategory-Strict-Category C
  pr2 preunivalent-category-Strict-Category = is-preunivalent-Strict-Category
```

### Precomposition by a morphism

```agda
precomp-hom-Strict-Category :
  {l1 l2 : Level} (C : Strict-Category l1 l2) {x y : obj-Strict-Category C}
  (f : hom-Strict-Category C x y) (z : obj-Strict-Category C) →
  hom-Strict-Category C y z → hom-Strict-Category C x z
precomp-hom-Strict-Category C =
  precomp-hom-Precategory (precategory-Strict-Category C)
```

### Postcomposition by a morphism

```agda
postcomp-hom-Strict-Category :
  {l1 l2 : Level} (C : Strict-Category l1 l2) {x y : obj-Strict-Category C}
  (f : hom-Strict-Category C x y) (z : obj-Strict-Category C) →
  hom-Strict-Category C z x → hom-Strict-Category C z y
postcomp-hom-Strict-Category C =
  postcomp-hom-Precategory (precategory-Strict-Category C)
```

### Equalities induce morphisms

```agda
module _
  {l1 l2 : Level} (C : Strict-Category l1 l2)
  where

  hom-eq-Strict-Category :
    (x y : obj-Strict-Category C) → x ＝ y → hom-Strict-Category C x y
  hom-eq-Strict-Category = hom-eq-Precategory (precategory-Strict-Category C)

  hom-inv-eq-Strict-Category :
    (x y : obj-Strict-Category C) → x ＝ y → hom-Strict-Category C y x
  hom-inv-eq-Strict-Category =
    hom-inv-eq-Precategory (precategory-Strict-Category C)
```
