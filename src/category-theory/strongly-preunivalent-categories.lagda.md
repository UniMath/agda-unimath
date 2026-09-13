# Strongly preunivalent categories

```agda
module category-theory.strongly-preunivalent-categories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.composition-operations-on-binary-families-of-sets
open import category-theory.isomorphisms-in-precategories
open import category-theory.precategories
open import category-theory.preunivalent-categories

open import foundation.1-types
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.dependent-products-propositions
open import foundation.embeddings
open import foundation.equality-dependent-pair-types
open import foundation.equivalences
open import foundation.fibers-of-maps
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

A
{{#concept "strongly preunivalent category" Agda=Strongly-Preunivalent-Category}}
`𝒞` is a [precategory](category-theory.precategories.md) for which every mapping
of the concrete groupoid of objects into the groupoid of
[isomorphisms](category-theory.isomorphisms-in-precategories.md) is an
[embedding](foundation-core.embeddings.md). Equivalently, by
[subuniverse equality duality](foundation.structured-equality-duality.md), a
strongly preunivalent category is a precategory whose based isomorphism types
`Σ (x : 𝒞₀), (* ≅ x)` are [sets](foundation-core.sets.md).

The main purpose of _preunivalence_ is to serve as a common generalization of
univalent mathematics and mathematics with Axiom K by restricting the ways that
identity and equivalence may interact. Hence preunivalent categories generalize
both [(univalent) categories](category-theory.categories.md) and
[strict categories](category-theory.strict-categories.md), which are
precategories whose objects form a [set](foundation-core.sets.md). Note,
however, that our use of the term "preunivalence" here is in a
[stronger](foundation.strong-preunivalence.md) sense than its use in the
[preunivalence axiom](foundation.preunivalence.md).

## Definitions

### The predicate on precategories of being a strongly preunivalent category

We define strong preunivalence of a precategory `𝒞` to be the condition that for
every `x : 𝒞₀`, the type `Σ (y : 𝒞₀), (x ≅ y)` is a set.

```agda
module _
  {l1 l2 : Level} (𝒞 : Precategory l1 l2)
  where

  is-strongly-preunivalent-prop-Precategory : Prop (l1 ⊔ l2)
  is-strongly-preunivalent-prop-Precategory =
    Π-Prop
      ( obj-Precategory 𝒞)
      ( λ x →
        is-set-Prop
          ( Σ ( obj-Precategory 𝒞)
              ( iso-Precategory 𝒞 x)))

  is-strongly-preunivalent-Precategory : UU (l1 ⊔ l2)
  is-strongly-preunivalent-Precategory =
    type-Prop is-strongly-preunivalent-prop-Precategory

  is-preunivalent-is-strongly-preunivalent-Precategory :
    is-strongly-preunivalent-Precategory →
    is-preunivalent-Precategory 𝒞
  is-preunivalent-is-strongly-preunivalent-Precategory H x y =
    is-emb-is-prop-map
      ( backward-implication-structured-equality-duality
        ( is-prop-equiv')
        ( H x)
        ( x)
        ( iso-eq-Precategory 𝒞 x)
        ( y))
```

### The type of preunivalent categories

```agda
Strongly-Preunivalent-Category : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
Strongly-Preunivalent-Category l1 l2 =
  Σ (Precategory l1 l2) (is-strongly-preunivalent-Precategory)

module _
  {l1 l2 : Level} (𝒞 : Strongly-Preunivalent-Category l1 l2)
  where

  precategory-Strongly-Preunivalent-Category : Precategory l1 l2
  precategory-Strongly-Preunivalent-Category = pr1 𝒞

  obj-Strongly-Preunivalent-Category : UU l1
  obj-Strongly-Preunivalent-Category =
    obj-Precategory precategory-Strongly-Preunivalent-Category

  hom-set-Strongly-Preunivalent-Category :
    obj-Strongly-Preunivalent-Category →
    obj-Strongly-Preunivalent-Category →
    Set l2
  hom-set-Strongly-Preunivalent-Category =
    hom-set-Precategory precategory-Strongly-Preunivalent-Category

  hom-Strongly-Preunivalent-Category :
    obj-Strongly-Preunivalent-Category →
    obj-Strongly-Preunivalent-Category →
    UU l2
  hom-Strongly-Preunivalent-Category =
    hom-Precategory precategory-Strongly-Preunivalent-Category

  is-set-hom-Strongly-Preunivalent-Category :
    (x y : obj-Strongly-Preunivalent-Category) →
    is-set (hom-Strongly-Preunivalent-Category x y)
  is-set-hom-Strongly-Preunivalent-Category =
    is-set-hom-Precategory precategory-Strongly-Preunivalent-Category

  comp-hom-Strongly-Preunivalent-Category :
    {x y z : obj-Strongly-Preunivalent-Category} →
    hom-Strongly-Preunivalent-Category y z →
    hom-Strongly-Preunivalent-Category x y →
    hom-Strongly-Preunivalent-Category x z
  comp-hom-Strongly-Preunivalent-Category =
    comp-hom-Precategory precategory-Strongly-Preunivalent-Category

  associative-comp-hom-Strongly-Preunivalent-Category :
    {x y z w : obj-Strongly-Preunivalent-Category}
    (h : hom-Strongly-Preunivalent-Category z w)
    (g : hom-Strongly-Preunivalent-Category y z)
    (f : hom-Strongly-Preunivalent-Category x y) →
    comp-hom-Strongly-Preunivalent-Category
      ( comp-hom-Strongly-Preunivalent-Category h g)
      ( f) ＝
    comp-hom-Strongly-Preunivalent-Category
      ( h)
      ( comp-hom-Strongly-Preunivalent-Category g f)
  associative-comp-hom-Strongly-Preunivalent-Category =
    associative-comp-hom-Precategory precategory-Strongly-Preunivalent-Category

  involutive-eq-associative-comp-hom-Strongly-Preunivalent-Category :
    {x y z w : obj-Strongly-Preunivalent-Category}
    (h : hom-Strongly-Preunivalent-Category z w)
    (g : hom-Strongly-Preunivalent-Category y z)
    (f : hom-Strongly-Preunivalent-Category x y) →
    comp-hom-Strongly-Preunivalent-Category
      ( comp-hom-Strongly-Preunivalent-Category h g)
      ( f) ＝ⁱ
    comp-hom-Strongly-Preunivalent-Category
      ( h)
      ( comp-hom-Strongly-Preunivalent-Category g f)
  involutive-eq-associative-comp-hom-Strongly-Preunivalent-Category =
    involutive-eq-associative-comp-hom-Precategory
      ( precategory-Strongly-Preunivalent-Category)

  associative-composition-operation-Strongly-Preunivalent-Category :
    associative-composition-operation-binary-family-Set
      hom-set-Strongly-Preunivalent-Category
  associative-composition-operation-Strongly-Preunivalent-Category =
    associative-composition-operation-Precategory
      ( precategory-Strongly-Preunivalent-Category)

  id-hom-Strongly-Preunivalent-Category :
    {x : obj-Strongly-Preunivalent-Category} →
    hom-Strongly-Preunivalent-Category x x
  id-hom-Strongly-Preunivalent-Category =
    id-hom-Precategory precategory-Strongly-Preunivalent-Category

  left-unit-law-comp-hom-Strongly-Preunivalent-Category :
    {x y : obj-Strongly-Preunivalent-Category}
    (f : hom-Strongly-Preunivalent-Category x y) →
    comp-hom-Strongly-Preunivalent-Category
      ( id-hom-Strongly-Preunivalent-Category)
      ( f) ＝
    f
  left-unit-law-comp-hom-Strongly-Preunivalent-Category =
    left-unit-law-comp-hom-Precategory
      precategory-Strongly-Preunivalent-Category

  right-unit-law-comp-hom-Strongly-Preunivalent-Category :
    {x y : obj-Strongly-Preunivalent-Category}
    (f : hom-Strongly-Preunivalent-Category x y) →
    comp-hom-Strongly-Preunivalent-Category
      ( f)
      ( id-hom-Strongly-Preunivalent-Category) ＝
    f
  right-unit-law-comp-hom-Strongly-Preunivalent-Category =
    right-unit-law-comp-hom-Precategory
      precategory-Strongly-Preunivalent-Category

  is-unital-composition-operation-Strongly-Preunivalent-Category :
    is-unital-composition-operation-binary-family-Set
      hom-set-Strongly-Preunivalent-Category
      comp-hom-Strongly-Preunivalent-Category
  is-unital-composition-operation-Strongly-Preunivalent-Category =
    is-unital-composition-operation-Precategory
      ( precategory-Strongly-Preunivalent-Category)

  is-strongly-preunivalent-Strongly-Preunivalent-Category :
    is-strongly-preunivalent-Precategory
      precategory-Strongly-Preunivalent-Category
  is-strongly-preunivalent-Strongly-Preunivalent-Category = pr2 𝒞

  iso-Strongly-Preunivalent-Category :
    (x y : obj-Strongly-Preunivalent-Category) → UU l2
  iso-Strongly-Preunivalent-Category =
    iso-Precategory precategory-Strongly-Preunivalent-Category

  iso-eq-Strongly-Preunivalent-Category :
    (x y : obj-Strongly-Preunivalent-Category) →
    x ＝ y → iso-Strongly-Preunivalent-Category x y
  iso-eq-Strongly-Preunivalent-Category =
    iso-eq-Precategory precategory-Strongly-Preunivalent-Category

  is-preunivalent-Strongly-Preunivalent-Category :
    is-preunivalent-Precategory precategory-Strongly-Preunivalent-Category
  is-preunivalent-Strongly-Preunivalent-Category =
    is-preunivalent-is-strongly-preunivalent-Precategory
      ( precategory-Strongly-Preunivalent-Category)
      ( is-strongly-preunivalent-Strongly-Preunivalent-Category)

  emb-iso-eq-Strongly-Preunivalent-Category :
    {x y : obj-Strongly-Preunivalent-Category} →
    (x ＝ y) ↪ (iso-Precategory precategory-Strongly-Preunivalent-Category x y)
  emb-iso-eq-Strongly-Preunivalent-Category {x} {y} =
    ( iso-eq-Precategory precategory-Strongly-Preunivalent-Category x y ,
      is-preunivalent-Strongly-Preunivalent-Category x y)
```

### The right-based isomorphism types of a strongly preunivalent category are also sets

```agda
is-strongly-preunivalent-Strongly-Preunivalent-Category' :
  {l1 l2 : Level} (𝒞 : Strongly-Preunivalent-Category l1 l2) →
  ( x : obj-Strongly-Preunivalent-Category 𝒞) →
  is-set
    ( Σ ( obj-Strongly-Preunivalent-Category 𝒞)
        ( λ y → iso-Strongly-Preunivalent-Category 𝒞 y x))
is-strongly-preunivalent-Strongly-Preunivalent-Category' 𝒞 x =
  is-set-equiv
    ( Σ ( obj-Strongly-Preunivalent-Category 𝒞)
        ( iso-Strongly-Preunivalent-Category 𝒞 x))
    ( equiv-tot
      ( λ y →
        equiv-inv-iso-Precategory
          ( precategory-Strongly-Preunivalent-Category 𝒞)))
    ( is-strongly-preunivalent-Strongly-Preunivalent-Category 𝒞 x)
```

### The total hom-type of a strongly preunivalent category

```agda
total-hom-Strongly-Preunivalent-Category :
  {l1 l2 : Level} (𝒞 : Strongly-Preunivalent-Category l1 l2) → UU (l1 ⊔ l2)
total-hom-Strongly-Preunivalent-Category 𝒞 =
  total-hom-Precategory (precategory-Strongly-Preunivalent-Category 𝒞)

obj-total-hom-Strongly-Preunivalent-Category :
  {l1 l2 : Level} (𝒞 : Strongly-Preunivalent-Category l1 l2) →
  total-hom-Strongly-Preunivalent-Category 𝒞 →
  obj-Strongly-Preunivalent-Category 𝒞 × obj-Strongly-Preunivalent-Category 𝒞
obj-total-hom-Strongly-Preunivalent-Category 𝒞 =
  obj-total-hom-Precategory (precategory-Strongly-Preunivalent-Category 𝒞)
```

### Equalities induce morphisms

```agda
module _
  {l1 l2 : Level}
  (𝒞 : Strongly-Preunivalent-Category l1 l2)
  where

  hom-eq-Strongly-Preunivalent-Category :
    (x y : obj-Strongly-Preunivalent-Category 𝒞) →
    x ＝ y → hom-Strongly-Preunivalent-Category 𝒞 x y
  hom-eq-Strongly-Preunivalent-Category =
    hom-eq-Precategory (precategory-Strongly-Preunivalent-Category 𝒞)

  hom-inv-eq-Strongly-Preunivalent-Category :
    (x y : obj-Strongly-Preunivalent-Category 𝒞) →
    x ＝ y → hom-Strongly-Preunivalent-Category 𝒞 y x
  hom-inv-eq-Strongly-Preunivalent-Category =
    hom-inv-eq-Precategory (precategory-Strongly-Preunivalent-Category 𝒞)
```

### Pre- and postcomposition by a morphism

```agda
precomp-hom-Strongly-Preunivalent-Category :
  {l1 l2 : Level} (𝒞 : Strongly-Preunivalent-Category l1 l2)
  {x y : obj-Strongly-Preunivalent-Category 𝒞}
  (f : hom-Strongly-Preunivalent-Category 𝒞 x y)
  (z : obj-Strongly-Preunivalent-Category 𝒞) →
  hom-Strongly-Preunivalent-Category 𝒞 y z →
  hom-Strongly-Preunivalent-Category 𝒞 x z
precomp-hom-Strongly-Preunivalent-Category 𝒞 =
  precomp-hom-Precategory (precategory-Strongly-Preunivalent-Category 𝒞)

postcomp-hom-Strongly-Preunivalent-Category :
  {l1 l2 : Level} (𝒞 : Strongly-Preunivalent-Category l1 l2)
  {x y : obj-Strongly-Preunivalent-Category 𝒞}
  (f : hom-Strongly-Preunivalent-Category 𝒞 x y)
  (z : obj-Strongly-Preunivalent-Category 𝒞) →
  hom-Strongly-Preunivalent-Category 𝒞 z x →
  hom-Strongly-Preunivalent-Category 𝒞 z y
postcomp-hom-Strongly-Preunivalent-Category 𝒞 =
  postcomp-hom-Precategory (precategory-Strongly-Preunivalent-Category 𝒞)
```

## Properties

### The objects in a strongly preunivalent category form a 1-type

The type of identities between two objects in a preunivalent category embeds
into the type of isomorphisms between them. But this type is a set, and thus the
identity type is a set.

```agda
module _
  {l1 l2 : Level} (𝒞 : Strongly-Preunivalent-Category l1 l2)
  where

  is-1-type-obj-Strongly-Preunivalent-Category :
    is-1-type (obj-Strongly-Preunivalent-Category 𝒞)
  is-1-type-obj-Strongly-Preunivalent-Category x y =
    is-set-is-emb
      ( iso-eq-Precategory (precategory-Strongly-Preunivalent-Category 𝒞) x y)
      ( is-preunivalent-Strongly-Preunivalent-Category 𝒞 x y)
      ( is-set-iso-Precategory (precategory-Strongly-Preunivalent-Category 𝒞))

  obj-1-type-Strongly-Preunivalent-Category : 1-Type l1
  pr1 obj-1-type-Strongly-Preunivalent-Category =
    obj-Strongly-Preunivalent-Category 𝒞
  pr2 obj-1-type-Strongly-Preunivalent-Category =
    is-1-type-obj-Strongly-Preunivalent-Category
```

### The total hom-type of a strongly preunivalent category is a 1-type

```agda
module _
  {l1 l2 : Level} (𝒞 : Strongly-Preunivalent-Category l1 l2)
  where

  is-1-type-total-hom-Strongly-Preunivalent-Category :
    is-1-type (total-hom-Strongly-Preunivalent-Category 𝒞)
  is-1-type-total-hom-Strongly-Preunivalent-Category =
    is-trunc-total-hom-is-trunc-obj-Precategory
      ( precategory-Strongly-Preunivalent-Category 𝒞)
      ( is-1-type-obj-Strongly-Preunivalent-Category 𝒞)

  total-hom-1-type-Strongly-Preunivalent-Category : 1-Type (l1 ⊔ l2)
  total-hom-1-type-Strongly-Preunivalent-Category =
    total-hom-truncated-type-is-trunc-obj-Precategory
      ( precategory-Strongly-Preunivalent-Category 𝒞)
      ( is-1-type-obj-Strongly-Preunivalent-Category 𝒞)
```

## Preunivalent categories are strongly preunivalent

```agda
is-strongly-preunivalent-is-preunivalent-Precategory :
  {l1 l2 : Level} (𝒞 : Precategory l1 l2) →
  is-preunivalent-Precategory 𝒞 → is-strongly-preunivalent-Precategory 𝒞
is-strongly-preunivalent-is-preunivalent-Precategory 𝒞 pua x (y , α) (y' , α') =
  is-prop-equiv
    ( equivalence-reasoning
      ( (y , α) ＝ (y' , α'))
      ≃ Eq-Σ (y , α) (y' , α') by equiv-pair-eq-Σ (y , α) (y' , α')
      ≃ fiber
          ( iso-eq-Precategory 𝒞 y y')
          ( comp-iso-Precategory 𝒞 α' (inv-iso-Precategory 𝒞 α))
      by
        equiv-tot
        ( λ where
          refl →
            equivalence-reasoning
            (α ＝ α')
            ≃ ( comp-iso-Precategory 𝒞 α (inv-iso-Precategory 𝒞 α) ＝
                comp-iso-Precategory 𝒞 α' (inv-iso-Precategory 𝒞 α))
              by
                equiv-ap
                  ( equiv-precomp-iso-Precategory 𝒞 (inv-iso-Precategory 𝒞 α) y)
                  ( α)
                  ( α')
            ≃ ( id-iso-Precategory 𝒞 ＝
                comp-iso-Precategory 𝒞 α' (inv-iso-Precategory 𝒞 α))
              by
              equiv-concat
                ( inv (right-inverse-law-comp-iso-Precategory 𝒞 α))
                ( comp-iso-Precategory 𝒞 α' (inv-iso-Precategory 𝒞 α))))
    ( is-prop-map-is-emb
      ( pua y y')
      ( comp-iso-Precategory 𝒞 α' (inv-iso-Precategory 𝒞 α)))
```

## See also

- [The strong preunivalence axiom](foundation.strong-preunivalence.md)
