# Opposite strongly preunivalent categories

```agda
module category-theory.opposite-strongly-preunivalent-categories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.isomorphisms-in-precategories
open import category-theory.opposite-precategories
open import category-theory.precategories
open import category-theory.strongly-preunivalent-categories

open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.equivalences
open import foundation.functoriality-dependent-pair-types
open import foundation.identity-types
open import foundation.involutions
open import foundation.sets
open import foundation.strictly-involutive-identity-types
open import foundation.subtypes
open import foundation.universe-levels
```

</details>

## Idea

Let `𝒞` be a
[strongly preunivalent category](category-theory.strongly-preunivalent-categories.md),
its **opposite strongly preunivalent category** `𝒞ᵒᵖ` is given by reversing
every morphism.

## Lemma

### A precategory is strongly preunivalent if and only if the opposite is strongly preunivalent

```agda
abstract
  is-strongly-preunivalent-opposite-is-strongly-preunivalent-Precategory :
    {l1 l2 : Level} (𝒞 : Precategory l1 l2) →
    is-strongly-preunivalent-Precategory 𝒞 →
    is-strongly-preunivalent-Precategory (opposite-Precategory 𝒞)
  is-strongly-preunivalent-opposite-is-strongly-preunivalent-Precategory
    𝒞 is-strongly-preunivalent-𝒞 x =
    is-set-equiv'
      ( Σ (obj-opposite-Precategory 𝒞) (iso-Precategory 𝒞 x))
      ( equiv-tot
        ( λ _ →
          compute-iso-opposite-Precategory 𝒞 ∘e equiv-inv-iso-Precategory 𝒞))
      ( is-strongly-preunivalent-𝒞 x)

abstract
  is-strongly-preunivalent-is-strongly-preunivalent-opposite-Precategory :
    {l1 l2 : Level} (𝒞 : Precategory l1 l2) →
    is-strongly-preunivalent-Precategory (opposite-Precategory 𝒞) →
    is-strongly-preunivalent-Precategory 𝒞
  is-strongly-preunivalent-is-strongly-preunivalent-opposite-Precategory 𝒞 =
    is-strongly-preunivalent-opposite-is-strongly-preunivalent-Precategory
      ( opposite-Precategory 𝒞)
```

## Definitions

### The opposite strongly preunivalent category

```agda
module _
  {l1 l2 : Level} (𝒞 : Strongly-Preunivalent-Category l1 l2)
  where

  obj-opposite-Strongly-Preunivalent-Category : UU l1
  obj-opposite-Strongly-Preunivalent-Category =
    obj-opposite-Precategory (precategory-Strongly-Preunivalent-Category 𝒞)

  hom-set-opposite-Strongly-Preunivalent-Category :
    (x y : obj-opposite-Strongly-Preunivalent-Category) → Set l2
  hom-set-opposite-Strongly-Preunivalent-Category =
    hom-set-opposite-Precategory (precategory-Strongly-Preunivalent-Category 𝒞)

  hom-opposite-Strongly-Preunivalent-Category :
    (x y : obj-opposite-Strongly-Preunivalent-Category) → UU l2
  hom-opposite-Strongly-Preunivalent-Category =
    hom-opposite-Precategory (precategory-Strongly-Preunivalent-Category 𝒞)

  comp-hom-opposite-Strongly-Preunivalent-Category :
    {x y z : obj-opposite-Strongly-Preunivalent-Category} →
    hom-opposite-Strongly-Preunivalent-Category y z →
    hom-opposite-Strongly-Preunivalent-Category x y →
    hom-opposite-Strongly-Preunivalent-Category x z
  comp-hom-opposite-Strongly-Preunivalent-Category =
    comp-hom-opposite-Precategory (precategory-Strongly-Preunivalent-Category 𝒞)

  involutive-eq-associative-comp-hom-opposite-Strongly-Preunivalent-Category :
    {x y z w : obj-opposite-Strongly-Preunivalent-Category}
    (h : hom-opposite-Strongly-Preunivalent-Category z w)
    (g : hom-opposite-Strongly-Preunivalent-Category y z)
    (f : hom-opposite-Strongly-Preunivalent-Category x y) →
    comp-hom-opposite-Strongly-Preunivalent-Category
      ( comp-hom-opposite-Strongly-Preunivalent-Category h g)
      ( f) ＝ⁱ
    comp-hom-opposite-Strongly-Preunivalent-Category
      ( h)
      ( comp-hom-opposite-Strongly-Preunivalent-Category g f)
  involutive-eq-associative-comp-hom-opposite-Strongly-Preunivalent-Category =
    involutive-eq-associative-comp-hom-opposite-Precategory
      ( precategory-Strongly-Preunivalent-Category 𝒞)

  associative-comp-hom-opposite-Strongly-Preunivalent-Category :
    {x y z w : obj-opposite-Strongly-Preunivalent-Category}
    (h : hom-opposite-Strongly-Preunivalent-Category z w)
    (g : hom-opposite-Strongly-Preunivalent-Category y z)
    (f : hom-opposite-Strongly-Preunivalent-Category x y) →
    comp-hom-opposite-Strongly-Preunivalent-Category
      ( comp-hom-opposite-Strongly-Preunivalent-Category h g)
      ( f) ＝
    comp-hom-opposite-Strongly-Preunivalent-Category
      ( h)
      ( comp-hom-opposite-Strongly-Preunivalent-Category g f)
  associative-comp-hom-opposite-Strongly-Preunivalent-Category =
    associative-comp-hom-opposite-Precategory
      ( precategory-Strongly-Preunivalent-Category 𝒞)

  id-hom-opposite-Strongly-Preunivalent-Category :
    {x : obj-opposite-Strongly-Preunivalent-Category} →
    hom-opposite-Strongly-Preunivalent-Category x x
  id-hom-opposite-Strongly-Preunivalent-Category =
    id-hom-opposite-Precategory (precategory-Strongly-Preunivalent-Category 𝒞)

  left-unit-law-comp-hom-opposite-Strongly-Preunivalent-Category :
    {x y : obj-opposite-Strongly-Preunivalent-Category}
    (f : hom-opposite-Strongly-Preunivalent-Category x y) →
    comp-hom-opposite-Strongly-Preunivalent-Category
      ( id-hom-opposite-Strongly-Preunivalent-Category)
      ( f) ＝
    f
  left-unit-law-comp-hom-opposite-Strongly-Preunivalent-Category =
    left-unit-law-comp-hom-opposite-Precategory
      ( precategory-Strongly-Preunivalent-Category 𝒞)

  right-unit-law-comp-hom-opposite-Strongly-Preunivalent-Category :
    {x y : obj-opposite-Strongly-Preunivalent-Category}
    (f : hom-opposite-Strongly-Preunivalent-Category x y) →
    comp-hom-opposite-Strongly-Preunivalent-Category
      ( f) (id-hom-opposite-Strongly-Preunivalent-Category) ＝
    ( f)
  right-unit-law-comp-hom-opposite-Strongly-Preunivalent-Category =
    right-unit-law-comp-hom-opposite-Precategory
      ( precategory-Strongly-Preunivalent-Category 𝒞)

  precategory-opposite-Strongly-Preunivalent-Category : Precategory l1 l2
  precategory-opposite-Strongly-Preunivalent-Category =
    opposite-Precategory (precategory-Strongly-Preunivalent-Category 𝒞)

  opposite-Strongly-Preunivalent-Category : Strongly-Preunivalent-Category l1 l2
  pr1 opposite-Strongly-Preunivalent-Category =
    precategory-opposite-Strongly-Preunivalent-Category
  pr2 opposite-Strongly-Preunivalent-Category =
    is-strongly-preunivalent-opposite-is-strongly-preunivalent-Precategory
      ( precategory-Strongly-Preunivalent-Category 𝒞)
      ( is-strongly-preunivalent-Strongly-Preunivalent-Category 𝒞)
```

## Properties

### The opposite construction is an involution on the type of preunivalent categories

```agda
is-involution-opposite-Strongly-Preunivalent-Category :
  {l1 l2 : Level} →
  is-involution (opposite-Strongly-Preunivalent-Category {l1} {l2})
is-involution-opposite-Strongly-Preunivalent-Category 𝒞 =
  eq-type-subtype
    ( is-strongly-preunivalent-prop-Precategory)
    ( is-involution-opposite-Precategory
      ( precategory-Strongly-Preunivalent-Category 𝒞))

involution-opposite-Strongly-Preunivalent-Category :
  (l1 l2 : Level) → involution (Strongly-Preunivalent-Category l1 l2)
pr1 (involution-opposite-Strongly-Preunivalent-Category l1 l2) =
  opposite-Strongly-Preunivalent-Category
pr2 (involution-opposite-Strongly-Preunivalent-Category l1 l2) =
  is-involution-opposite-Strongly-Preunivalent-Category

is-equiv-opposite-Strongly-Preunivalent-Category :
  {l1 l2 : Level} → is-equiv (opposite-Strongly-Preunivalent-Category {l1} {l2})
is-equiv-opposite-Strongly-Preunivalent-Category =
  is-equiv-is-involution is-involution-opposite-Strongly-Preunivalent-Category

equiv-opposite-Strongly-Preunivalent-Category :
  (l1 l2 : Level) →
  Strongly-Preunivalent-Category l1 l2 ≃ Strongly-Preunivalent-Category l1 l2
equiv-opposite-Strongly-Preunivalent-Category l1 l2 =
  equiv-involution (involution-opposite-Strongly-Preunivalent-Category l1 l2)
```

## External links

- [Precategories - opposites](https://1lab.dev/Cat.Base.html#opposites) at 1lab
- [opposite category](https://ncatlab.org/nlab/show/opposite+category) at $n$Lab
- [Opposite category](https://en.wikipedia.org/wiki/Opposite_category) at
  Wikipedia
- [opposite category](https://www.wikidata.org/wiki/Q7098616) at Wikidata
