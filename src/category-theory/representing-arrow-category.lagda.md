# The representing arrow category

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module category-theory.representing-arrow-category
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import category-theory.categories funext univalence truncations
open import category-theory.isomorphisms-in-precategories funext univalence truncations
open import category-theory.precategories funext univalence truncations

open import foundation.dependent-pair-types
open import foundation.dependent-products-propositions funext
open import foundation.empty-types funext univalence truncations
open import foundation.identity-types funext
open import foundation.logical-equivalences funext
open import foundation.propositions funext univalence
open import foundation.sets funext univalence
open import foundation.subtypes funext univalence truncations
open import foundation.unit-type
open import foundation.universe-levels

open import foundation-core.booleans
```

</details>

## Idea

The **representing arrow** is the [category](category-theory.categories.md) that
[represents](category-theory.representable-functors-categories.md) arrows in a
([pre-](category-theory.precategories.md))category. We model it after
implication on the [booleans](foundation-core.booleans.md).

## Definition

### The objects and hom-sets of the representing arrow

```agda
obj-representing-arrow-Category : UU lzero
obj-representing-arrow-Category = bool

hom-set-representing-arrow-Category :
  obj-representing-arrow-Category → obj-representing-arrow-Category → Set lzero
hom-set-representing-arrow-Category true true = unit-Set
hom-set-representing-arrow-Category true false = empty-Set
hom-set-representing-arrow-Category false _ = unit-Set

hom-representing-arrow-Category :
  obj-representing-arrow-Category → obj-representing-arrow-Category → UU lzero
hom-representing-arrow-Category x y =
  type-Set (hom-set-representing-arrow-Category x y)
```

### The underlying precategory of the representing arrow

```agda
comp-hom-representing-arrow-Category :
  {x y z : obj-representing-arrow-Category} →
  hom-representing-arrow-Category y z →
  hom-representing-arrow-Category x y →
  hom-representing-arrow-Category x z
comp-hom-representing-arrow-Category {true} {true} {true} _ _ = star
comp-hom-representing-arrow-Category {false} _ _ = star

associative-comp-hom-representing-arrow-Category :
  {x y z w : obj-representing-arrow-Category} →
  (h : hom-representing-arrow-Category z w)
  (g : hom-representing-arrow-Category y z)
  (f : hom-representing-arrow-Category x y) →
  ( comp-hom-representing-arrow-Category
    { x} (comp-hom-representing-arrow-Category {y} h g) f) ＝
  ( comp-hom-representing-arrow-Category
    { x} h (comp-hom-representing-arrow-Category {x} g f))
associative-comp-hom-representing-arrow-Category
  { true} {true} {true} {true} h g f =
  refl
associative-comp-hom-representing-arrow-Category {false} h g f = refl

id-hom-representing-arrow-Category :
  {x : obj-representing-arrow-Category} → hom-representing-arrow-Category x x
id-hom-representing-arrow-Category {true} = star
id-hom-representing-arrow-Category {false} = star

left-unit-law-comp-hom-representing-arrow-Category :
  {x y : obj-representing-arrow-Category} →
  (f : hom-representing-arrow-Category x y) →
  comp-hom-representing-arrow-Category
    { x} (id-hom-representing-arrow-Category {y}) f ＝
  f
left-unit-law-comp-hom-representing-arrow-Category {true} {true} f = refl
left-unit-law-comp-hom-representing-arrow-Category {false} f = refl

right-unit-law-comp-hom-representing-arrow-Category :
  {x y : obj-representing-arrow-Category} →
  (f : hom-representing-arrow-Category x y) →
  comp-hom-representing-arrow-Category
    { x} f (id-hom-representing-arrow-Category {x}) ＝
  f
right-unit-law-comp-hom-representing-arrow-Category {true} {true} f = refl
right-unit-law-comp-hom-representing-arrow-Category {false} f = refl

representing-arrow-Precategory : Precategory lzero lzero
representing-arrow-Precategory =
  make-Precategory
    ( obj-representing-arrow-Category)
    ( hom-set-representing-arrow-Category)
    ( λ {x} {y} {z} → comp-hom-representing-arrow-Category {x} {y} {z})
    ( λ x → id-hom-representing-arrow-Category {x})
    ( λ {x} {y} {z} {w} →
      associative-comp-hom-representing-arrow-Category {x} {y} {z} {w})
    ( λ {x} {y} → left-unit-law-comp-hom-representing-arrow-Category {x} {y})
    ( λ {x} {y} → right-unit-law-comp-hom-representing-arrow-Category {x} {y})
```

### The representing arrow category

```agda
is-category-representing-arrow-Category :
  is-category-Precategory representing-arrow-Precategory
is-category-representing-arrow-Category true true =
    is-equiv-has-converse-is-prop
    ( is-set-bool true true)
    ( is-prop-type-subtype
      ( is-iso-prop-Precategory representing-arrow-Precategory {true} {true})
      ( is-prop-unit))
    ( λ _ → refl)
is-category-representing-arrow-Category true false =
  is-equiv-is-empty
    ( iso-eq-Precategory representing-arrow-Precategory true false)
    ( hom-iso-Precategory representing-arrow-Precategory)
is-category-representing-arrow-Category false true =
  is-equiv-is-empty
    ( iso-eq-Precategory representing-arrow-Precategory false true)
    ( hom-inv-iso-Precategory representing-arrow-Precategory)
is-category-representing-arrow-Category false false =
  is-equiv-has-converse-is-prop
    ( is-set-bool false false)
    ( is-prop-type-subtype
      ( is-iso-prop-Precategory representing-arrow-Precategory {false} {false})
      ( is-prop-unit))
    ( λ _ → refl)

representing-arrow-Category : Category lzero lzero
pr1 representing-arrow-Category = representing-arrow-Precategory
pr2 representing-arrow-Category = is-category-representing-arrow-Category
```

## Properties

### The representing arrow represents arrows in a category

This remains to be formalized.

## External links

- [Interval category](https://1lab.dev/Cat.Instances.Shape.Interval.html#interval-category)
  at 1lab
- [interval category](https://ncatlab.org/nlab/show/interval+category) at $n$Lab

A wikidata identifier was not available for this concept.
