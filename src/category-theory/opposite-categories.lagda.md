# Opposite categories

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module category-theory.opposite-categories
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import category-theory.categories funext univalence truncations
open import category-theory.isomorphisms-in-precategories funext univalence truncations
open import category-theory.opposite-precategories funext univalence truncations
open import category-theory.precategories funext univalence truncations

open import foundation.dependent-pair-types
open import foundation.equivalences funext
open import foundation.identity-types funext
open import foundation.involutions funext univalence
open import foundation.sets funext univalence
open import foundation.strictly-involutive-identity-types funext univalence
open import foundation.subtypes funext univalence truncations
open import foundation.universe-levels
```

</details>

## Idea

Let `C` be a [category](category-theory.categories.md), its **opposite
category** `Cᵒᵖ` is given by reversing every morphism.

## Lemma

### The underlying precategory is a category if and only if the opposite is a category

```agda
abstract
  is-category-opposite-is-category-Precategory :
    {l1 l2 : Level} (C : Precategory l1 l2) →
    is-category-Precategory C →
    is-category-Precategory (opposite-Precategory C)
  is-category-opposite-is-category-Precategory C is-category-C x y =
    is-equiv-htpy-equiv
      ( compute-iso-opposite-Precategory C ∘e
        equiv-inv-iso-Precategory C ∘e
        (_ , is-category-C x y))
      ( λ where
        refl →
          eq-type-subtype
            ( is-iso-prop-Precategory (opposite-Precategory C))
            ( refl))

abstract
  is-category-is-category-opposite-Precategory :
    {l1 l2 : Level} (C : Precategory l1 l2) →
    is-category-Precategory (opposite-Precategory C) →
    is-category-Precategory C
  is-category-is-category-opposite-Precategory C =
    is-category-opposite-is-category-Precategory (opposite-Precategory C)
```

## Definitions

### The opposite category

```agda
module _
  {l1 l2 : Level} (C : Category l1 l2)
  where

  obj-opposite-Category : UU l1
  obj-opposite-Category = obj-opposite-Precategory (precategory-Category C)

  hom-set-opposite-Category : (x y : obj-opposite-Category) → Set l2
  hom-set-opposite-Category =
    hom-set-opposite-Precategory (precategory-Category C)

  hom-opposite-Category : (x y : obj-opposite-Category) → UU l2
  hom-opposite-Category = hom-opposite-Precategory (precategory-Category C)

  comp-hom-opposite-Category :
    {x y z : obj-opposite-Category} →
    hom-opposite-Category y z →
    hom-opposite-Category x y →
    hom-opposite-Category x z
  comp-hom-opposite-Category =
    comp-hom-opposite-Precategory (precategory-Category C)

  associative-comp-hom-opposite-Category :
    {x y z w : obj-opposite-Category}
    (h : hom-opposite-Category z w)
    (g : hom-opposite-Category y z)
    (f : hom-opposite-Category x y) →
    comp-hom-opposite-Category (comp-hom-opposite-Category h g) f ＝
    comp-hom-opposite-Category h (comp-hom-opposite-Category g f)
  associative-comp-hom-opposite-Category =
    associative-comp-hom-opposite-Precategory (precategory-Category C)

  involutive-eq-associative-comp-hom-opposite-Category :
    {x y z w : obj-opposite-Category}
    (h : hom-opposite-Category z w)
    (g : hom-opposite-Category y z)
    (f : hom-opposite-Category x y) →
    comp-hom-opposite-Category (comp-hom-opposite-Category h g) f ＝ⁱ
    comp-hom-opposite-Category h (comp-hom-opposite-Category g f)
  involutive-eq-associative-comp-hom-opposite-Category =
    involutive-eq-associative-comp-hom-opposite-Precategory
      ( precategory-Category C)

  id-hom-opposite-Category :
    {x : obj-opposite-Category} → hom-opposite-Category x x
  id-hom-opposite-Category =
    id-hom-opposite-Precategory (precategory-Category C)

  left-unit-law-comp-hom-opposite-Category :
    {x y : obj-opposite-Category}
    (f : hom-opposite-Category x y) →
    comp-hom-opposite-Category id-hom-opposite-Category f ＝ f
  left-unit-law-comp-hom-opposite-Category =
    left-unit-law-comp-hom-opposite-Precategory (precategory-Category C)

  right-unit-law-comp-hom-opposite-Category :
    {x y : obj-opposite-Category} (f : hom-opposite-Category x y) →
    comp-hom-opposite-Category f id-hom-opposite-Category ＝ f
  right-unit-law-comp-hom-opposite-Category =
    right-unit-law-comp-hom-opposite-Precategory (precategory-Category C)

  precategory-opposite-Category : Precategory l1 l2
  precategory-opposite-Category = opposite-Precategory (precategory-Category C)

  opposite-Category : Category l1 l2
  pr1 opposite-Category = precategory-opposite-Category
  pr2 opposite-Category =
    is-category-opposite-is-category-Precategory
      ( precategory-Category C)
      ( is-category-Category C)
```

## Properties

### The opposite construction is an involution on the type of categories

```agda
is-involution-opposite-Category :
  {l1 l2 : Level} → is-involution (opposite-Category {l1} {l2})
is-involution-opposite-Category C =
  eq-type-subtype
    ( is-category-prop-Precategory)
    ( is-involution-opposite-Precategory (precategory-Category C))

involution-opposite-Category :
  (l1 l2 : Level) → involution (Category l1 l2)
pr1 (involution-opposite-Category l1 l2) = opposite-Category
pr2 (involution-opposite-Category l1 l2) = is-involution-opposite-Category

is-equiv-opposite-Category :
  {l1 l2 : Level} → is-equiv (opposite-Category {l1} {l2})
is-equiv-opposite-Category =
  is-equiv-is-involution is-involution-opposite-Category

equiv-opposite-Category :
  (l1 l2 : Level) → Category l1 l2 ≃ Category l1 l2
equiv-opposite-Category l1 l2 =
  equiv-involution (involution-opposite-Category l1 l2)
```

## External links

- [Precategories - opposites](https://1lab.dev/Cat.Base.html#opposites) at 1lab
- [opposite category](https://ncatlab.org/nlab/show/opposite+category) at $n$Lab
- [Opposite category](https://en.wikipedia.org/wiki/Opposite_category) at
  Wikipedia
- [opposite category](https://www.wikidata.org/wiki/Q7098616) at Wikidata
