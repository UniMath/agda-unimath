# The terminal category

```agda
module category-theory.terminal-category where
```

<details><summary>Imports</summary>

```agda
open import category-theory.categories
open import category-theory.composition-operations-on-binary-families-of-sets
open import category-theory.functors-categories
open import category-theory.isomorphisms-in-precategories
open import category-theory.precategories
open import category-theory.yoneda-lemma-categories
open import category-theory.strict-categories

open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.unit-type
open import foundation.contractible-types
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

terminal-Precategory : Precategory lzero lzero
pr1 terminal-Precategory = obj-terminal-Category
pr1 (pr2 terminal-Precategory) = hom-set-terminal-Category
pr1 (pr2 (pr2 terminal-Precategory)) =
  associative-composition-operation-terminal-Category
pr2 (pr2 (pr2 terminal-Precategory)) =
  is-unital-composition-operation-terminal-Category
```

### The terminal category

```agda
is-category-terminal-Category :
  is-category-Precategory terminal-Precategory
is-category-terminal-Category x y =
  is-equiv-is-contr
    ( iso-eq-Precategory terminal-Precategory x y)
    ( is-prop-is-contr is-contr-unit x y)
    ( is-contr-Σ is-contr-unit star
      ( is-proof-irrelevant-is-prop
        ( is-prop-is-iso-Precategory terminal-Precategory star)
        ( star , refl , refl)))

terminal-Category : Category lzero lzero
pr1 terminal-Category = terminal-Precategory
pr2 terminal-Category = is-category-terminal-Category
```

## Properties

### The terminal category represents objects

This is a consequence of the
[Yoneda lemma](category-theory.yoneda-lemma-categories.md).

### The terminal category is strict

```agda
is-strict-category-terminal-Category :
  is-strict-category-Precategory terminal-Precategory
is-strict-category-terminal-Category = is-set-unit
```

### The terminal category is a poset

This remains to be formalized.

### The terminal category is gaunt

This remains to be formalized.

## See also

- [The initial category](category-theory.initial-category.lagda.md)

## External links

- [Terminal category](https://1lab.dev/Cat.Instances.Shape.Terminal.html) at
  1lab
- [Terminal category](https://ncatlab.org/nlab/show/terminal+category) at nlab

A wikidata identifier was not available for this concept.
