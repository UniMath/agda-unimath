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
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.strictly-involutive-identity-types
open import foundation.universe-levels
```

</details>

## Idea

A {{#concept "preunivalent category" Agda=Preunivalent-Category}} is a
[precategory](category-theory.precategories.md) `𝒞` for which the
[identifications](foundation-core.identity-types.md) between objects
[embed](foundation-core.embeddings.md) into the
[isomorphisms](category-theory.isomorphisms-in-precategories.md) via the
particular inductively defined map

```text
  iso-eq : (x y : 𝒞₀) → x ＝ y → x ≅ y
  iso-eq x .x refl := id-iso x.
```

The main purpose of _preunivalence_ is to serve as a common generalization of
univalent mathematics and mathematics with Axiom K by restricting the ways that
identity and equivalence may interact. Hence preunivalent categories generalize
both [(univalent) categories](category-theory.categories.md) and
[strict categories](category-theory.strict-categories.md), which are
precategories whose objects form a [set](foundation-core.sets.md).

Notice, however, that while preunivalent categories are _a_ common
generalization of univalent and strict categories, they are not the greatest
common generalization. For instance, both univalent and strict categories
satisfy the further property that _every_ map of type
`(x y : 𝒞₀) → x ＝ y → x ≅ y` is an embedding. For univalent categories this
follows by uniqueness of the identity family, and for strict categories this
follows from the fact that equality is a proposition. This observation leads to
a stronger generalization, called
[strongly preunivalent categories](category-theory.strongly-preunivalent-categories.md).

## Definitions

### The predicate on precategories of being a preunivalent category

```agda
module _
  {l1 l2 : Level} (𝒞 : Precategory l1 l2)
  where

  is-preunivalent-prop-Precategory : Prop (l1 ⊔ l2)
  is-preunivalent-prop-Precategory =
    Π-Prop
      ( obj-Precategory 𝒞)
      ( λ x →
        Π-Prop
          ( obj-Precategory 𝒞)
          ( λ y → is-emb-Prop (iso-eq-Precategory 𝒞 x y)))

  is-preunivalent-Precategory : UU (l1 ⊔ l2)
  is-preunivalent-Precategory = type-Prop is-preunivalent-prop-Precategory
```

### The type of preunivalent categories

```agda
Preunivalent-Category : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
Preunivalent-Category l1 l2 =
  Σ (Precategory l1 l2) (is-preunivalent-Precategory)

module _
  {l1 l2 : Level} (𝒞 : Preunivalent-Category l1 l2)
  where

  precategory-Preunivalent-Category : Precategory l1 l2
  precategory-Preunivalent-Category = pr1 𝒞

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

  involutive-eq-associative-comp-hom-Preunivalent-Category :
    {x y z w : obj-Preunivalent-Category}
    (h : hom-Preunivalent-Category z w)
    (g : hom-Preunivalent-Category y z)
    (f : hom-Preunivalent-Category x y) →
    comp-hom-Preunivalent-Category (comp-hom-Preunivalent-Category h g) f ＝ⁱ
    comp-hom-Preunivalent-Category h (comp-hom-Preunivalent-Category g f)
  involutive-eq-associative-comp-hom-Preunivalent-Category =
    involutive-eq-associative-comp-hom-Precategory
      ( precategory-Preunivalent-Category)

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
  is-preunivalent-Preunivalent-Category = pr2 𝒞

  emb-iso-eq-Preunivalent-Category :
    {x y : obj-Preunivalent-Category} →
    (x ＝ y) ↪ (iso-Precategory precategory-Preunivalent-Category x y)
  pr1 (emb-iso-eq-Preunivalent-Category {x} {y}) =
    iso-eq-Precategory precategory-Preunivalent-Category x y
  pr2 (emb-iso-eq-Preunivalent-Category {x} {y}) =
    is-preunivalent-Preunivalent-Category x y
```

### The total hom-type of a preunivalent category

```agda
total-hom-Preunivalent-Category :
  {l1 l2 : Level} (𝒞 : Preunivalent-Category l1 l2) → UU (l1 ⊔ l2)
total-hom-Preunivalent-Category 𝒞 =
  total-hom-Precategory (precategory-Preunivalent-Category 𝒞)

obj-total-hom-Preunivalent-Category :
  {l1 l2 : Level} (𝒞 : Preunivalent-Category l1 l2) →
  total-hom-Preunivalent-Category 𝒞 →
  obj-Preunivalent-Category 𝒞 × obj-Preunivalent-Category 𝒞
obj-total-hom-Preunivalent-Category 𝒞 =
  obj-total-hom-Precategory (precategory-Preunivalent-Category 𝒞)
```

### Equalities induce morphisms

```agda
module _
  {l1 l2 : Level}
  (𝒞 : Preunivalent-Category l1 l2)
  where

  hom-eq-Preunivalent-Category :
    (x y : obj-Preunivalent-Category 𝒞) →
    x ＝ y → hom-Preunivalent-Category 𝒞 x y
  hom-eq-Preunivalent-Category =
    hom-eq-Precategory (precategory-Preunivalent-Category 𝒞)

  hom-inv-eq-Preunivalent-Category :
    (x y : obj-Preunivalent-Category 𝒞) →
    x ＝ y → hom-Preunivalent-Category 𝒞 y x
  hom-inv-eq-Preunivalent-Category =
    hom-inv-eq-Precategory (precategory-Preunivalent-Category 𝒞)
```

### Pre- and postcomposition by a morphism

```agda
precomp-hom-Preunivalent-Category :
  {l1 l2 : Level} (𝒞 : Preunivalent-Category l1 l2)
  {x y : obj-Preunivalent-Category 𝒞}
  (f : hom-Preunivalent-Category 𝒞 x y)
  (z : obj-Preunivalent-Category 𝒞) →
  hom-Preunivalent-Category 𝒞 y z →
  hom-Preunivalent-Category 𝒞 x z
precomp-hom-Preunivalent-Category 𝒞 =
  precomp-hom-Precategory (precategory-Preunivalent-Category 𝒞)

postcomp-hom-Preunivalent-Category :
  {l1 l2 : Level} (𝒞 : Preunivalent-Category l1 l2)
  {x y : obj-Preunivalent-Category 𝒞}
  (f : hom-Preunivalent-Category 𝒞 x y)
  (z : obj-Preunivalent-Category 𝒞) →
  hom-Preunivalent-Category 𝒞 z x →
  hom-Preunivalent-Category 𝒞 z y
postcomp-hom-Preunivalent-Category 𝒞 =
  postcomp-hom-Precategory (precategory-Preunivalent-Category 𝒞)
```

## Properties

### The objects in a preunivalent category form a 1-type

The type of identities between two objects in a preunivalent category embeds
into the type of isomorphisms between them. But this type is a set, and thus the
identity type is a set.

```agda
module _
  {l1 l2 : Level} (𝒞 : Preunivalent-Category l1 l2)
  where

  is-1-type-obj-Preunivalent-Category : is-1-type (obj-Preunivalent-Category 𝒞)
  is-1-type-obj-Preunivalent-Category x y =
    is-set-is-emb
      ( iso-eq-Precategory (precategory-Preunivalent-Category 𝒞) x y)
      ( is-preunivalent-Preunivalent-Category 𝒞 x y)
      ( is-set-iso-Precategory (precategory-Preunivalent-Category 𝒞))

  obj-1-type-Preunivalent-Category : 1-Type l1
  pr1 obj-1-type-Preunivalent-Category = obj-Preunivalent-Category 𝒞
  pr2 obj-1-type-Preunivalent-Category = is-1-type-obj-Preunivalent-Category
```

### The total hom-type of a preunivalent category is a 1-type

```agda
module _
  {l1 l2 : Level} (𝒞 : Preunivalent-Category l1 l2)
  where

  is-1-type-total-hom-Preunivalent-Category :
    is-1-type (total-hom-Preunivalent-Category 𝒞)
  is-1-type-total-hom-Preunivalent-Category =
    is-trunc-total-hom-is-trunc-obj-Precategory
      ( precategory-Preunivalent-Category 𝒞)
      ( is-1-type-obj-Preunivalent-Category 𝒞)

  total-hom-1-type-Preunivalent-Category : 1-Type (l1 ⊔ l2)
  total-hom-1-type-Preunivalent-Category =
    total-hom-truncated-type-is-trunc-obj-Precategory
      ( precategory-Preunivalent-Category 𝒞)
      ( is-1-type-obj-Preunivalent-Category 𝒞)
```

## See also

- [The preunivalence axiom](foundation.preunivalence.md)
