# Preunivalent categories

```agda
module category-theory.preunivalent-categories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.composition-operations-on-binary-families-of-sets
open import category-theory.isomorphisms-in-precategories
open import category-theory.precategories

open import foundation.1-types
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.universe-levels
```

</details>

## Idea

A **preunivalent category** is a [precategory](category-theory.precategories.md)
for which the [identifications](foundation-core.identity-types.md) between the
objects [embed](foundation-core.embeddings.md) into the
[isomorphisms](category-theory.isomorphisms-in-precategories.md). More
specifically, an equality between objects gives rise to an isomorphism between
them, by the J-rule. A precategory is a preunivalent category if this function,
called `iso-eq`, is an embedding. In particular. being preunivalent is a
[proposition](foundation-core.propositions.md) since `is-emb` is a proposition.

The idea of preunivalence is that it is a common generalization of univalent
mathematics and mathematics with Axiom K. Hence preunivalent categories
generalize both [categories](category-theory.categories.md) in the sense we have
defined them (as univalent categories), and strict categories, which are
precategories whose objects form a [set](foundation-core.sets.md).

## Definitions

```agda
module _
  {l1 l2 : Level} (C : Precategory l1 l2)
  where

  is-preunivalent-prop-Precategory : Prop (l1 ⊔ l2)
  is-preunivalent-prop-Precategory =
    Π-Prop
      ( obj-Precategory C)
      ( λ x →
        Π-Prop
          ( obj-Precategory C)
          ( λ y → is-emb-Prop (iso-eq-Precategory C x y)))

  is-preunivalent-Precategory : UU (l1 ⊔ l2)
  is-preunivalent-Precategory = type-Prop is-preunivalent-prop-Precategory

Preunivalent-Category : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
Preunivalent-Category l1 l2 =
  Σ (Precategory l1 l2) (is-preunivalent-Precategory)

module _
  {l1 l2 : Level} (C : Preunivalent-Category l1 l2)
  where

  precategory-Preunivalent-Category : Precategory l1 l2
  precategory-Preunivalent-Category = pr1 C

  obj-Preunivalent-Category : UU l1
  obj-Preunivalent-Category = obj-Precategory precategory-Preunivalent-Category

  hom-set-Preunivalent-Category :
    obj-Preunivalent-Category → obj-Preunivalent-Category → Set l2
  hom-set-Preunivalent-Category =
    hom-set-Precategory precategory-Preunivalent-Category

  hom-Preunivalent-Category :
    obj-Preunivalent-Category → obj-Preunivalent-Category → UU l2
  hom-Preunivalent-Category = hom-Precategory precategory-Preunivalent-Category

  is-set-hom-Preunivalent-Category :
    (x y : obj-Preunivalent-Category) → is-set (hom-Preunivalent-Category x y)
  is-set-hom-Preunivalent-Category =
    is-set-hom-Precategory precategory-Preunivalent-Category

  comp-hom-Preunivalent-Category :
    {x y z : obj-Preunivalent-Category} →
    hom-Preunivalent-Category y z →
    hom-Preunivalent-Category x y →
    hom-Preunivalent-Category x z
  comp-hom-Preunivalent-Category =
    comp-hom-Precategory precategory-Preunivalent-Category

  associative-comp-hom-Preunivalent-Category :
    {x y z w : obj-Preunivalent-Category}
    (h : hom-Preunivalent-Category z w)
    (g : hom-Preunivalent-Category y z)
    (f : hom-Preunivalent-Category x y) →
    comp-hom-Preunivalent-Category (comp-hom-Preunivalent-Category h g) f ＝
    comp-hom-Preunivalent-Category h (comp-hom-Preunivalent-Category g f)
  associative-comp-hom-Preunivalent-Category =
    associative-comp-hom-Precategory precategory-Preunivalent-Category

  associative-composition-operation-Preunivalent-Category :
    associative-composition-operation-binary-family-Set
      hom-set-Preunivalent-Category
  associative-composition-operation-Preunivalent-Category =
    associative-composition-operation-Precategory
      ( precategory-Preunivalent-Category)

  id-hom-Preunivalent-Category :
    {x : obj-Preunivalent-Category} → hom-Preunivalent-Category x x
  id-hom-Preunivalent-Category =
    id-hom-Precategory precategory-Preunivalent-Category

  left-unit-law-comp-hom-Preunivalent-Category :
    {x y : obj-Preunivalent-Category} (f : hom-Preunivalent-Category x y) →
    comp-hom-Preunivalent-Category id-hom-Preunivalent-Category f ＝ f
  left-unit-law-comp-hom-Preunivalent-Category =
    left-unit-law-comp-hom-Precategory precategory-Preunivalent-Category

  right-unit-law-comp-hom-Preunivalent-Category :
    {x y : obj-Preunivalent-Category} (f : hom-Preunivalent-Category x y) →
    comp-hom-Preunivalent-Category f id-hom-Preunivalent-Category ＝ f
  right-unit-law-comp-hom-Preunivalent-Category =
    right-unit-law-comp-hom-Precategory precategory-Preunivalent-Category

  is-unital-composition-operation-Preunivalent-Category :
    is-unital-composition-operation-binary-family-Set
      hom-set-Preunivalent-Category
      comp-hom-Preunivalent-Category
  is-unital-composition-operation-Preunivalent-Category =
    is-unital-composition-operation-Precategory
      ( precategory-Preunivalent-Category)

  is-preunivalent-Preunivalent-Category :
    is-preunivalent-Precategory precategory-Preunivalent-Category
  is-preunivalent-Preunivalent-Category = pr2 C
```

### Precomposition by a morphism

```agda
precomp-hom-Preunivalent-Category :
  {l1 l2 : Level} (C : Preunivalent-Category l1 l2)
  {x y : obj-Preunivalent-Category C}
  (f : hom-Preunivalent-Category C x y)
  (z : obj-Preunivalent-Category C) →
  hom-Preunivalent-Category C y z →
  hom-Preunivalent-Category C x z
precomp-hom-Preunivalent-Category C =
  precomp-hom-Precategory (precategory-Preunivalent-Category C)
```

### Postcomposition by a morphism

```agda
postcomp-hom-Preunivalent-Category :
  {l1 l2 : Level} (C : Preunivalent-Category l1 l2)
  {x y : obj-Preunivalent-Category C}
  (f : hom-Preunivalent-Category C x y)
  (z : obj-Preunivalent-Category C) →
  hom-Preunivalent-Category C z x →
  hom-Preunivalent-Category C z y
postcomp-hom-Preunivalent-Category C =
  postcomp-hom-Precategory (precategory-Preunivalent-Category C)
```

### Equalities induce morphisms

```agda
module _
  {l1 l2 : Level}
  (C : Preunivalent-Category l1 l2)
  where

  hom-eq-Preunivalent-Category :
    (x y : obj-Preunivalent-Category C) →
    x ＝ y → hom-Preunivalent-Category C x y
  hom-eq-Preunivalent-Category =
    hom-eq-Precategory (precategory-Preunivalent-Category C)

  hom-inv-eq-Preunivalent-Category :
    (x y : obj-Preunivalent-Category C) →
    x ＝ y → hom-Preunivalent-Category C y x
  hom-inv-eq-Preunivalent-Category =
    hom-inv-eq-Precategory (precategory-Preunivalent-Category C)
```

## Properties

### The objects in a preunivalent category form a 1-type

The type of identities between two objects in a preunivalent category embeds
into the type of isomorphisms between them. But this type is a set, and thus the
identity type is a set.

```agda
module _
  {l1 l2 : Level} (C : Preunivalent-Category l1 l2)
  where

  is-1-type-obj-Preunivalent-Category : is-1-type (obj-Preunivalent-Category C)
  is-1-type-obj-Preunivalent-Category x y =
    is-set-is-emb
      ( iso-eq-Precategory (precategory-Preunivalent-Category C) x y)
      ( is-preunivalent-Preunivalent-Category C x y)
      ( is-set-iso-Precategory (precategory-Preunivalent-Category C))

  obj-1-type-Preunivalent-Category : 1-Type l1
  pr1 obj-1-type-Preunivalent-Category = obj-Preunivalent-Category C
  pr2 obj-1-type-Preunivalent-Category = is-1-type-obj-Preunivalent-Category
```

## See also

- [Axiom L](foundation.axiom-l.md)
