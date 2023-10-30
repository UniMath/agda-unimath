# The terminal category

```agda
module category-theory.terminal-category where
```

<details><summary>Imports</summary>

```agda
open import category-theory.categories
open import category-theory.composition-operations-on-binary-families-of-sets
open import category-theory.isomorphisms-in-precategories
open import category-theory.precategories

open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.unit-type
open import foundation.sets
open import foundation.subtypes
open import foundation.unit-type
open import foundation.universe-levels
```

</details>

## Idea

The **terminal category** is the [category](category-theory.categories.md) with
one object and only the identity on that object. This category
[represents](category-theory.representable-functors-categories.md) objects.

## Definition

### The objects and hom-sets of the representing arrow

```agda
obj-terminal-Category : UU lzero
obj-terminal-Category = unit

hom-set-terminal-Category :
  obj-terminal-Category → obj-terminal-Category → Set lzero
hom-set-terminal-Category x x₁ = unit-Set

hom-terminal-Category :
  obj-terminal-Category → obj-terminal-Category → UU lzero
hom-terminal-Category x y = type-Set (hom-set-terminal-Category x y)
```

### The underlying precategory of the terminal category

```agda
comp-hom-terminal-Category :
  {x y z : obj-terminal-Category} →
  hom-terminal-Category y z →
  hom-terminal-Category x y →
  hom-terminal-Category x z
comp-hom-terminal-Category _ _ = star

associative-comp-hom-terminal-Category :
  {x y z w : obj-terminal-Category} →
  (h : hom-terminal-Category z w)
  (g : hom-terminal-Category y z)
  (f : hom-terminal-Category x y) →
  comp-hom-terminal-Category {x} (comp-hom-terminal-Category {y} h g) f ＝
  comp-hom-terminal-Category {x} h (comp-hom-terminal-Category {x} g f)
associative-comp-hom-terminal-Category h g f = refl

associative-composition-operation-terminal-Category :
  associative-composition-operation-binary-family-Set hom-set-terminal-Category
pr1 associative-composition-operation-terminal-Category {x} =
  comp-hom-terminal-Category {x}
pr2 associative-composition-operation-terminal-Category =
  associative-comp-hom-terminal-Category

id-hom-terminal-Category :
  {x : obj-terminal-Category} → hom-terminal-Category x x
id-hom-terminal-Category = star

left-unit-law-comp-hom-terminal-Category :
  {x y : obj-terminal-Category} →
  (f : hom-terminal-Category x y) →
  comp-hom-terminal-Category {x} (id-hom-terminal-Category {y}) f ＝ f
left-unit-law-comp-hom-terminal-Category f = refl

right-unit-law-comp-hom-terminal-Category :
  {x y : obj-terminal-Category} →
  (f : hom-terminal-Category x y) →
  comp-hom-terminal-Category {x} f (id-hom-terminal-Category {x}) ＝ f
right-unit-law-comp-hom-terminal-Category f = refl

is-unital-composition-operation-terminal-Category :
  is-unital-composition-operation-binary-family-Set
    ( hom-set-terminal-Category)
    ( λ {x} {y} {z} → comp-hom-terminal-Category {x} {y} {z})
pr1 is-unital-composition-operation-terminal-Category x =
  id-hom-terminal-Category {x}
pr1 (pr2 is-unital-composition-operation-terminal-Category) =
  left-unit-law-comp-hom-terminal-Category
pr2 (pr2 is-unital-composition-operation-terminal-Category) =
  right-unit-law-comp-hom-terminal-Category

precategory-terminal-Category : Precategory lzero lzero
pr1 precategory-terminal-Category = obj-terminal-Category
pr1 (pr2 precategory-terminal-Category) = hom-set-terminal-Category
pr1 (pr2 (pr2 precategory-terminal-Category)) =
  associative-composition-operation-terminal-Category
pr2 (pr2 (pr2 precategory-terminal-Category)) =
  is-unital-composition-operation-terminal-Category
```

### The representing arrow category

```text
is-category-terminal-Category :
  is-category-Precategory precategory-terminal-Category
is-category-terminal-Category true true =
    is-equiv-is-prop
    ( is-set-bool true true)
    ( is-prop-type-subtype
      ( is-iso-prop-Precategory
        ( precategory-terminal-Category) {true} {true})
      ( is-prop-unit))
    ( λ _ → refl)
is-category-terminal-Category true false =
  is-equiv-is-empty
    ( iso-eq-Precategory precategory-terminal-Category true false)
    ( hom-iso-Precategory precategory-terminal-Category)
is-category-terminal-Category false true =
  is-equiv-is-empty
    ( iso-eq-Precategory precategory-terminal-Category false true)
    ( hom-inv-iso-Precategory precategory-terminal-Category)
is-category-terminal-Category false false =
  is-equiv-is-prop
    ( is-set-bool false false)
    ( is-prop-type-subtype
      ( is-iso-prop-Precategory
        ( precategory-terminal-Category) {false} {false})
      ( is-prop-unit))
    ( λ _ → refl)

terminal-Category-Category : Category lzero lzero
pr1 terminal-Category-Category = precategory-terminal-Category
pr2 terminal-Category-Category = is-category-terminal-Category
```

## Properties

### The terminal category represent objects

This is a consequence of the
[Yoneda lemma](category-theory.yoneda-lemma-categories.md).

### The terminal category is gaunt

### The terminal category is strict

### The terminal category is a poset

## See also

- [The initial category](category-theory.initial-category.lagda.md)

## External links
