# Categories

```agda
module category-theory.categories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.isomorphisms-precategories
open import category-theory.precategories

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

A category in Homotopy Type Theory is a precategory for which the identities
between the objects are the isomorphisms. More specifically, an equality between
objects gives rise to an isomorphism between them, by the J-rule. A precategory
is a category if this function is an equivalence. Note: being a category is a
proposition since `is-equiv` is a proposition.

## Definition

```agda
module _
  {l1 l2 : Level} (C : Precategory l1 l2)
  where

  is-category-Precategory-Prop : Prop (l1 ⊔ l2)
  is-category-Precategory-Prop =
    Π-Prop
      ( obj-Precategory C)
      ( λ x →
        Π-Prop
          ( obj-Precategory C)
          ( λ y → is-equiv-Prop (iso-eq-Precategory C x y)))

  is-category-Precategory : UU (l1 ⊔ l2)
  is-category-Precategory = type-Prop is-category-Precategory-Prop

Category : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
Category l1 l2 = Σ (Precategory l1 l2) is-category-Precategory

module _
  {l1 l2 : Level} (C : Category l1 l2)
  where

  precategory-Category : Precategory l1 l2
  precategory-Category = pr1 C

  obj-Category : UU l1
  obj-Category = obj-Precategory precategory-Category

  hom-Category : obj-Category → obj-Category → Set l2
  hom-Category = hom-Precategory precategory-Category

  type-hom-Category : obj-Category → obj-Category → UU l2
  type-hom-Category = type-hom-Precategory precategory-Category

  is-set-type-hom-Category :
    (x y : obj-Category) → is-set (type-hom-Category x y)
  is-set-type-hom-Category = is-set-type-hom-Precategory precategory-Category

  comp-hom-Category :
    {x y z : obj-Category} →
    type-hom-Category y z → type-hom-Category x y → type-hom-Category x z
  comp-hom-Category = comp-hom-Precategory precategory-Category

  associative-comp-hom-Category :
    {x y z w : obj-Category}
    (h : type-hom-Category z w)
    (g : type-hom-Category y z)
    (f : type-hom-Category x y) →
    comp-hom-Category (comp-hom-Category h g) f ＝
    comp-hom-Category h (comp-hom-Category g f)
  associative-comp-hom-Category =
    associative-comp-hom-Precategory precategory-Category

  id-hom-Category : {x : obj-Category} → type-hom-Category x x
  id-hom-Category = id-hom-Precategory precategory-Category

  left-unit-law-comp-hom-Category :
    {x y : obj-Category} (f : type-hom-Category x y) →
    comp-hom-Category id-hom-Category f ＝ f
  left-unit-law-comp-hom-Category =
    left-unit-law-comp-hom-Precategory precategory-Category

  right-unit-law-comp-hom-Category :
    {x y : obj-Category} (f : type-hom-Category x y) →
    comp-hom-Category f id-hom-Category ＝ f
  right-unit-law-comp-hom-Category =
    right-unit-law-comp-hom-Precategory precategory-Category

  is-category-Category :
    is-category-Precategory precategory-Category
  is-category-Category = pr2 C
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
  is-1-type-obj-Category x y =
    is-set-is-equiv
      ( iso-Precategory (precategory-Category C) x y)
      ( iso-eq-Precategory (precategory-Category C) x y)
      ( is-category-Category C x y)
      ( is-set-iso-Precategory (precategory-Category C) x y)

  obj-Category-1-Type : 1-Type l1
  pr1 obj-Category-1-Type = obj-Category C
  pr2 obj-Category-1-Type = is-1-type-obj-Category
```
