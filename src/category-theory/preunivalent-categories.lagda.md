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
open import foundation.functoriality-dependent-pair-types
open import foundation.identity-types
open import foundation.propositional-maps
open import foundation.propositions
open import foundation.sets
open import foundation.strictly-involutive-identity-types
open import foundation.structured-equality-duality
open import foundation.universe-levels
```

</details>

## Idea

A {{#concept "preunivalent category" Agda=Preunivalent-Category}} `𝒞` is a
[precategory](category-theory.precategories.md) for which every mapping of the
concrete groupoid of objects into the groupoid of
[isomorphisms](category-theory.isomorphisms-in-precategories.md) is an
[embedding](foundation-core.embeddings.md). Equivalently, by
[subuniverse equality duality](foundation.structured-equality-duality.md), a
preunivalent category is a precategory whose based isomorphism types
`Σ (x : 𝒞₀), (* ≅ x)` are [sets](foundation-core.sets.md).

The main purpose of _preunivalence_ is to serve as a common generalization of
univalent mathematics and mathematics with Axiom K by restricting the ways that
identity and equivalence may interact. Hence preunivalent categories generalize
both [(univalent) categories](category-theory.categories.md) and
[strict categories](category-theory.strict-categories.md), which are
precategories whose objects form a [set](foundation-core.sets.md). Note,
however, that our use of the term "preunivalence" here is in a
[stronger](foundation.strong-preunivalence.md) sense its use in the
[preunivalence axiom](foundation.preunivalence.md).

## Definitions

### The predicate on precategories of being a preunivalent category

We define preunivalence of a precategory `𝒞` to be the condition that for every
`x : 𝒞₀`, the type `Σ (y : 𝒞₀), (x ≅ y)` is a set.

```agda
module _
  {l1 l2 : Level} (C : Precategory l1 l2)
  where

  is-preunivalent-prop-Precategory : Prop (l1 ⊔ l2)
  is-preunivalent-prop-Precategory =
    Π-Prop
      ( obj-Precategory C)
      ( λ x →
        is-set-Prop
          ( Σ ( obj-Precategory C)
              ( iso-Precategory C x)))

  is-preunivalent-Precategory : UU (l1 ⊔ l2)
  is-preunivalent-Precategory = type-Prop is-preunivalent-prop-Precategory

  preunivalence-is-preunivalent-Precategory :
    is-preunivalent-Precategory →
    (x y : obj-Precategory C) →
    is-emb (iso-eq-Precategory C x y)
  preunivalence-is-preunivalent-Precategory H x y =
    is-emb-is-prop-map
      ( backward-implication-subuniverse-equality-duality
        ( is-prop-Prop)
        (H x)
        ( x)
        ( iso-eq-Precategory C x)
        ( y))
```

### The type of preunivalent categories

```agda
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
  is-preunivalent-Preunivalent-Category = pr2 C

  iso-Preunivalent-Category : (x y : obj-Preunivalent-Category) → UU l2
  iso-Preunivalent-Category = iso-Precategory precategory-Preunivalent-Category

  iso-eq-Preunivalent-Category :
    (x y : obj-Preunivalent-Category) → x ＝ y → iso-Preunivalent-Category x y
  iso-eq-Preunivalent-Category =
    iso-eq-Precategory precategory-Preunivalent-Category

  preunivalence-Preunivalent-Category :
    (x y : obj-Preunivalent-Category) →
    is-emb (iso-eq-Preunivalent-Category x y)
  preunivalence-Preunivalent-Category =
    preunivalence-is-preunivalent-Precategory
      ( precategory-Preunivalent-Category)
      ( is-preunivalent-Preunivalent-Category)

  emb-iso-eq-Preunivalent-Category :
    {x y : obj-Preunivalent-Category} →
    (x ＝ y) ↪ (iso-Precategory precategory-Preunivalent-Category x y)
  emb-iso-eq-Preunivalent-Category {x} {y} =
    ( iso-eq-Precategory precategory-Preunivalent-Category x y ,
      preunivalence-Preunivalent-Category x y)
```

### The right-based isomorphism types of a preunivalent category are also sets

```agda
is-preunivalent-Preunivalent-Category' :
  {l1 l2 : Level} (C : Preunivalent-Category l1 l2) →
  ( x : obj-Preunivalent-Category C) →
  is-set
    ( Σ (obj-Preunivalent-Category C) (λ y → iso-Preunivalent-Category C y x))
is-preunivalent-Preunivalent-Category' C x =
  is-set-equiv
    ( Σ (obj-Preunivalent-Category C) (iso-Preunivalent-Category C x))
    ( equiv-tot
      ( λ y → equiv-inv-iso-Precategory (precategory-Preunivalent-Category C)))
    ( is-preunivalent-Preunivalent-Category C x)
```

### The total hom-type of a preunivalent category

```agda
total-hom-Preunivalent-Category :
  {l1 l2 : Level} (C : Preunivalent-Category l1 l2) → UU (l1 ⊔ l2)
total-hom-Preunivalent-Category C =
  total-hom-Precategory (precategory-Preunivalent-Category C)

obj-total-hom-Preunivalent-Category :
  {l1 l2 : Level} (C : Preunivalent-Category l1 l2) →
  total-hom-Preunivalent-Category C →
  obj-Preunivalent-Category C × obj-Preunivalent-Category C
obj-total-hom-Preunivalent-Category C =
  obj-total-hom-Precategory (precategory-Preunivalent-Category C)
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

### Pre- and postcomposition by a morphism

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
      ( preunivalence-Preunivalent-Category C x y)
      ( is-set-iso-Precategory (precategory-Preunivalent-Category C))

  obj-1-type-Preunivalent-Category : 1-Type l1
  pr1 obj-1-type-Preunivalent-Category = obj-Preunivalent-Category C
  pr2 obj-1-type-Preunivalent-Category = is-1-type-obj-Preunivalent-Category
```

### The total hom-type of a preunivalent category is a 1-type

```agda
module _
  {l1 l2 : Level} (C : Preunivalent-Category l1 l2)
  where

  is-1-type-total-hom-Preunivalent-Category :
    is-1-type (total-hom-Preunivalent-Category C)
  is-1-type-total-hom-Preunivalent-Category =
    is-trunc-total-hom-is-trunc-obj-Precategory
      ( precategory-Preunivalent-Category C)
      ( is-1-type-obj-Preunivalent-Category C)

  total-hom-1-type-Preunivalent-Category : 1-Type (l1 ⊔ l2)
  total-hom-1-type-Preunivalent-Category =
    total-hom-truncated-type-is-trunc-obj-Precategory
      ( precategory-Preunivalent-Category C)
      ( is-1-type-obj-Preunivalent-Category C)
```

## See also

- [The preunivalence axiom](foundation.preunivalence.md)
