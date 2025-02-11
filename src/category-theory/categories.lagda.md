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
open import category-theory.strongly-preunivalent-categories

open import foundation.1-types
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.fundamental-theorem-of-identity-types
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.propositions
open import foundation.sets
open import foundation.strictly-involutive-identity-types
open import foundation.surjective-maps
open import foundation.universe-levels
```

</details>

## Idea

A {{#concept "category" Agda=Category}} in Homotopy Type Theory is a
[precategory](category-theory.precategories.md) for which the
[identifications](foundation-core.identity-types.md) between the objects are the
[isomorphisms](category-theory.isomorphisms-in-precategories.md). More
specifically, an equality between objects gives rise to an isomorphism between
them, by the J-rule. A precategory is a category if this function, called
`iso-eq`, is an [equivalence](foundation-core.equivalences.md). In particular,
being a category is a [proposition](foundation-core.propositions.md) since
`is-equiv` is a proposition.

## Definitions

### The predicate on precategories of being a category

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

  is-prop-is-category-Precategory : is-prop is-category-Precategory
  is-prop-is-category-Precategory =
    is-prop-type-Prop is-category-prop-Precategory
```

### The type of categories

```agda
Category : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
Category l1 l2 = Σ (Precategory l1 l2) (is-category-Precategory)

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

  involutive-eq-associative-comp-hom-Category :
    {x y z w : obj-Category}
    (h : hom-Category z w)
    (g : hom-Category y z)
    (f : hom-Category x y) →
    comp-hom-Category (comp-hom-Category h g) f ＝ⁱ
    comp-hom-Category h (comp-hom-Category g f)
  involutive-eq-associative-comp-hom-Category =
    involutive-eq-associative-comp-hom-Precategory precategory-Category

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

### The underlying strongly preunivalent category of a category

```agda
module _
  {l1 l2 : Level} (C : Category l1 l2)
  where

  is-strongly-preunivalent-category-Category :
    is-strongly-preunivalent-Precategory (precategory-Category C)
  is-strongly-preunivalent-category-Category x =
    is-set-is-contr
      ( fundamental-theorem-id'
        ( iso-eq-Precategory (precategory-Category C) x)
        ( is-category-Category C x))

  strongly-preunivalent-category-Category : Strongly-Preunivalent-Category l1 l2
  strongly-preunivalent-category-Category =
    ( precategory-Category C , is-strongly-preunivalent-category-Category)
```

### The total hom-type of a category

```agda
total-hom-Category :
  {l1 l2 : Level} (C : Category l1 l2) → UU (l1 ⊔ l2)
total-hom-Category C = total-hom-Precategory (precategory-Category C)

obj-total-hom-Category :
  {l1 l2 : Level} (C : Category l1 l2) →
  total-hom-Category C →
  obj-Category C × obj-Category C
obj-total-hom-Category C = obj-total-hom-Precategory (precategory-Category C)
```

### Equalities induce morphisms

```agda
module _
  {l1 l2 : Level} (C : Category l1 l2) (x y : obj-Category C)
  where

  hom-eq-Category : x ＝ y → hom-Category C x y
  hom-eq-Category = hom-eq-Precategory (precategory-Category C) x y

  hom-inv-eq-Category : x ＝ y → hom-Category C y x
  hom-inv-eq-Category = hom-inv-eq-Precategory (precategory-Category C) x y
```

### Pre- and postcomposition by a morphism

```agda
precomp-hom-Category :
  {l1 l2 : Level} (C : Category l1 l2) {x y : obj-Category C}
  (f : hom-Category C x y) (z : obj-Category C) →
  hom-Category C y z → hom-Category C x z
precomp-hom-Category C = precomp-hom-Precategory (precategory-Category C)

postcomp-hom-Category :
  {l1 l2 : Level} (C : Category l1 l2) {x y : obj-Category C}
  (f : hom-Category C x y) (z : obj-Category C) →
  hom-Category C z x → hom-Category C z y
postcomp-hom-Category C = postcomp-hom-Precategory (precategory-Category C)
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
    is-1-type-obj-Strongly-Preunivalent-Category
      ( strongly-preunivalent-category-Category C)

  obj-1-type-Category : 1-Type l1
  obj-1-type-Category =
    obj-1-type-Strongly-Preunivalent-Category
      ( strongly-preunivalent-category-Category C)
```

### The total hom-type of a category is a 1-type

```agda
module _
  {l1 l2 : Level} (C : Category l1 l2)
  where

  is-1-type-total-hom-Category :
    is-1-type (total-hom-Category C)
  is-1-type-total-hom-Category =
    is-1-type-total-hom-Strongly-Preunivalent-Category
      ( strongly-preunivalent-category-Category C)

  total-hom-1-type-Category : 1-Type (l1 ⊔ l2)
  total-hom-1-type-Category =
    total-hom-1-type-Strongly-Preunivalent-Category
      ( strongly-preunivalent-category-Category C)
```

### A preunivalent category is a category if and only if `iso-eq` is surjective

```agda
module _
  {l1 l2 : Level} (C : Precategory l1 l2)
  where

  is-surjective-iso-eq-prop-Precategory : Prop (l1 ⊔ l2)
  is-surjective-iso-eq-prop-Precategory =
    Π-Prop
      ( obj-Precategory C)
      ( λ x →
        Π-Prop
          ( obj-Precategory C)
          ( λ y →
            is-surjective-Prop
              ( iso-eq-Precategory C x y)))

  is-surjective-iso-eq-Precategory : UU (l1 ⊔ l2)
  is-surjective-iso-eq-Precategory =
    type-Prop is-surjective-iso-eq-prop-Precategory

  is-prop-is-surjective-iso-eq-Precategory :
    is-prop is-surjective-iso-eq-Precategory
  is-prop-is-surjective-iso-eq-Precategory =
    is-prop-type-Prop is-surjective-iso-eq-prop-Precategory
```

```agda
module _
  {l1 l2 : Level} (C : Preunivalent-Category l1 l2)
  where

  is-category-is-surjective-iso-eq-Preunivalent-Category :
    is-surjective-iso-eq-Precategory (precategory-Preunivalent-Category C) →
    is-category-Precategory (precategory-Preunivalent-Category C)
  is-category-is-surjective-iso-eq-Preunivalent-Category
    is-surjective-iso-eq-C x y =
    is-equiv-is-emb-is-surjective
      ( is-surjective-iso-eq-C x y)
      ( is-preunivalent-Preunivalent-Category C x y)

  is-surjective-iso-eq-is-category-Preunivalent-Category :
    is-category-Precategory (precategory-Preunivalent-Category C) →
    is-surjective-iso-eq-Precategory (precategory-Preunivalent-Category C)
  is-surjective-iso-eq-is-category-Preunivalent-Category
    is-category-C x y =
    is-surjective-is-equiv (is-category-C x y)

  is-equiv-is-category-is-surjective-iso-eq-Preunivalent-Category :
    is-equiv is-category-is-surjective-iso-eq-Preunivalent-Category
  is-equiv-is-category-is-surjective-iso-eq-Preunivalent-Category =
    is-equiv-has-converse-is-prop
      ( is-prop-is-surjective-iso-eq-Precategory
        ( precategory-Preunivalent-Category C))
      ( is-prop-is-category-Precategory (precategory-Preunivalent-Category C))
      ( is-surjective-iso-eq-is-category-Preunivalent-Category)

  is-equiv-is-surjective-iso-eq-is-category-Preunivalent-Category :
    is-equiv is-surjective-iso-eq-is-category-Preunivalent-Category
  is-equiv-is-surjective-iso-eq-is-category-Preunivalent-Category =
    is-equiv-has-converse-is-prop
      ( is-prop-is-category-Precategory (precategory-Preunivalent-Category C))
      ( is-prop-is-surjective-iso-eq-Precategory
        ( precategory-Preunivalent-Category C))
      ( is-category-is-surjective-iso-eq-Preunivalent-Category)

  equiv-is-category-is-surjective-iso-eq-Preunivalent-Category :
    is-surjective-iso-eq-Precategory (precategory-Preunivalent-Category C) ≃
    is-category-Precategory (precategory-Preunivalent-Category C)
  pr1 equiv-is-category-is-surjective-iso-eq-Preunivalent-Category =
    is-category-is-surjective-iso-eq-Preunivalent-Category
  pr2 equiv-is-category-is-surjective-iso-eq-Preunivalent-Category =
    is-equiv-is-category-is-surjective-iso-eq-Preunivalent-Category

  equiv-is-surjective-iso-eq-is-category-Preunivalent-Category :
    is-category-Precategory (precategory-Preunivalent-Category C) ≃
    is-surjective-iso-eq-Precategory (precategory-Preunivalent-Category C)
  pr1 equiv-is-surjective-iso-eq-is-category-Preunivalent-Category =
    is-surjective-iso-eq-is-category-Preunivalent-Category
  pr2 equiv-is-surjective-iso-eq-is-category-Preunivalent-Category =
    is-equiv-is-surjective-iso-eq-is-category-Preunivalent-Category
```
