# Categories

```agda
module category-theory.categories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.isomorphisms-in-precategories
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

  associative-composition-structure-Category :
    associative-composition-structure-Set hom-set-Category
  associative-composition-structure-Category =
    associative-composition-structure-Precategory precategory-Category

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

  is-unital-composition-structure-Category :
    is-unital-composition-structure-Set
      hom-set-Category
      associative-composition-structure-Category
  is-unital-composition-structure-Category =
    is-unital-composition-structure-Precategory precategory-Category

  is-category-Category :
    is-category-Precategory precategory-Category
  is-category-Category = pr2 C
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

### Equalities give rise to homomorphisms

```agda
module _
  {l1 l2 : Level}
  (C : Category l1 l2)
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
  is-1-type-obj-Category x y =
    is-set-is-equiv
      ( iso-Precategory (precategory-Category C) x y)
      ( iso-eq-Precategory (precategory-Category C) x y)
      ( is-category-Category C x y)
      ( is-set-iso-Precategory (precategory-Category C))

  obj-Category-1-Type : 1-Type l1
  pr1 obj-Category-1-Type = obj-Category C
  pr2 obj-Category-1-Type = is-1-type-obj-Category
```
