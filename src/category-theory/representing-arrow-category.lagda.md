# The representing arrow category

```agda
module category-theory.representing-arrow-category where
```

<details><summary>Imports</summary>

```agda
open import category-theory.categories
open import category-theory.composition-operations-on-binary-families-of-sets
open import category-theory.isomorphisms-in-precategories
open import category-theory.precategories

open import foundation.booleans
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.subtypes
open import foundation.unit-type
open import foundation.universe-levels
```

</details>

## Idea

The **representing arrow** is the [category](category-theory.categories.md) that
[represents](category-theory.representable-functors-categories.md) arrows in a
([pre-](category-theory.precategories.md))category. We model it after
implication on the [booleans](foundation.booleans.md).

## Definition

### The objects and hom-sets of the representing arrow

```agda
obj-representing-arrow : UU lzero
obj-representing-arrow = bool

hom-set-representing-arrow :
  obj-representing-arrow → obj-representing-arrow → Set lzero
hom-set-representing-arrow true true = unit-Set
hom-set-representing-arrow true false = empty-Set
hom-set-representing-arrow false _ = unit-Set

hom-representing-arrow :
  obj-representing-arrow → obj-representing-arrow → UU lzero
hom-representing-arrow x y = type-Set (hom-set-representing-arrow x y)
```

### The underlying precategory of the representing arrow

```agda
comp-hom-representing-arrow :
  {x y z : obj-representing-arrow} →
  hom-representing-arrow y z →
  hom-representing-arrow x y →
  hom-representing-arrow x z
comp-hom-representing-arrow {true} {true} {true} _ _ = star
comp-hom-representing-arrow {false} _ _ = star

associative-comp-hom-representing-arrow :
  {x y z w : obj-representing-arrow} →
  (h : hom-representing-arrow z w)
  (g : hom-representing-arrow y z)
  (f : hom-representing-arrow x y) →
  comp-hom-representing-arrow {x} (comp-hom-representing-arrow {y} h g) f ＝
  comp-hom-representing-arrow {x} h (comp-hom-representing-arrow {x} g f)
associative-comp-hom-representing-arrow {true} {true} {true} {true} h g f = refl
associative-comp-hom-representing-arrow {false} h g f = refl

associative-composition-operation-representing-arrow :
  associative-composition-operation-binary-family-Set hom-set-representing-arrow
pr1 associative-composition-operation-representing-arrow {x} =
  comp-hom-representing-arrow {x}
pr2 associative-composition-operation-representing-arrow =
  associative-comp-hom-representing-arrow

id-hom-representing-arrow :
  {x : obj-representing-arrow} → hom-representing-arrow x x
id-hom-representing-arrow {true} = star
id-hom-representing-arrow {false} = star

left-unit-law-comp-hom-representing-arrow :
  {x y : obj-representing-arrow} →
  (f : hom-representing-arrow x y) →
  comp-hom-representing-arrow {x} (id-hom-representing-arrow {y}) f ＝ f
left-unit-law-comp-hom-representing-arrow {true} {true} f = refl
left-unit-law-comp-hom-representing-arrow {false} f = refl

right-unit-law-comp-hom-representing-arrow :
  {x y : obj-representing-arrow} →
  (f : hom-representing-arrow x y) →
  comp-hom-representing-arrow {x} f (id-hom-representing-arrow {x}) ＝ f
right-unit-law-comp-hom-representing-arrow {true} {true} f = refl
right-unit-law-comp-hom-representing-arrow {false} f = refl

is-unital-composition-operation-representing-arrow :
  is-unital-composition-operation-binary-family-Set
    ( hom-set-representing-arrow)
    ( λ {x} {y} {z} → comp-hom-representing-arrow {x} {y} {z})
pr1 is-unital-composition-operation-representing-arrow x =
  id-hom-representing-arrow {x}
pr1 (pr2 is-unital-composition-operation-representing-arrow) =
  left-unit-law-comp-hom-representing-arrow
pr2 (pr2 is-unital-composition-operation-representing-arrow) =
  right-unit-law-comp-hom-representing-arrow

representing-arrow-Precategory : Precategory lzero lzero
pr1 representing-arrow-Precategory = obj-representing-arrow
pr1 (pr2 representing-arrow-Precategory) = hom-set-representing-arrow
pr1 (pr2 (pr2 representing-arrow-Precategory)) =
  associative-composition-operation-representing-arrow
pr2 (pr2 (pr2 representing-arrow-Precategory)) =
  is-unital-composition-operation-representing-arrow
```

### The representing arrow category

```agda
is-category-representing-arrow :
  is-category-Precategory representing-arrow-Precategory
is-category-representing-arrow true true =
    is-equiv-is-prop
    ( is-set-bool true true)
    ( is-prop-type-subtype
      ( is-iso-prop-Precategory
        ( representing-arrow-Precategory) {true} {true})
      ( is-prop-unit))
    ( λ _ → refl)
is-category-representing-arrow true false =
  is-equiv-is-empty
    ( iso-eq-Precategory representing-arrow-Precategory true false)
    ( hom-iso-Precategory representing-arrow-Precategory)
is-category-representing-arrow false true =
  is-equiv-is-empty
    ( iso-eq-Precategory representing-arrow-Precategory false true)
    ( hom-inv-iso-Precategory representing-arrow-Precategory)
is-category-representing-arrow false false =
  is-equiv-is-prop
    ( is-set-bool false false)
    ( is-prop-type-subtype
      ( is-iso-prop-Precategory
        ( representing-arrow-Precategory) {false} {false})
      ( is-prop-unit))
    ( λ _ → refl)

representing-arrow-Category : Category lzero lzero
pr1 representing-arrow-Category = representing-arrow-Precategory
pr2 representing-arrow-Category = is-category-representing-arrow
```

## Properties

### The representing arrow represents arrows in a category

This is a consequence of the
[Yoneda lemma](category-theory.yoneda-lemma-categories.md).

## External links

- [Interval category](https://1lab.dev/Cat.Instances.Shape.Interval.html#interval-category)
  at 1lab
- [interval category](https://ncatlab.org/nlab/show/interval+category) at $n$Lab
