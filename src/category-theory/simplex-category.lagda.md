# The simplex category

```agda
module category-theory.simplex-category where
```

<details><summary>Imports</summary>

```agda
open import category-theory.categories
open import category-theory.precategories

open import elementary-number-theory.inequality-standard-finite-types
open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.homotopies
open import foundation.identity-types
open import foundation.sets
open import foundation.universe-levels

open import order-theory.order-preserving-maps-posets

open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

**The simplex category** is the category consisting of finite ordinals and
[order-preserving maps](order-theory.order-preserving-maps-posets.md).

## Definition

### The simplex precategory

```agda
obj-simplex-Category : UU lzero
obj-simplex-Category = ℕ

hom-set-simplex-Category :
  obj-simplex-Category → obj-simplex-Category → Set lzero
hom-set-simplex-Category n m =
  hom-set-Poset (Fin-Poset (succ-ℕ n)) (Fin-Poset (succ-ℕ m))

hom-simplex-Category :
  obj-simplex-Category → obj-simplex-Category → UU lzero
hom-simplex-Category n m = type-Set (hom-set-simplex-Category n m)

comp-hom-simplex-Category :
  {n m r : obj-simplex-Category} →
  hom-simplex-Category m r → hom-simplex-Category n m → hom-simplex-Category n r
comp-hom-simplex-Category {n} {m} {r} =
  comp-hom-Poset
    ( Fin-Poset (succ-ℕ n))
    ( Fin-Poset (succ-ℕ m))
    ( Fin-Poset (succ-ℕ r))

associative-comp-hom-simplex-Category :
  {n m r s : obj-simplex-Category}
  (h : hom-simplex-Category r s)
  (g : hom-simplex-Category m r)
  (f : hom-simplex-Category n m) →
  ( comp-hom-simplex-Category {n} {m} {s}
    ( comp-hom-simplex-Category {m} {r} {s} h g)
    ( f)) ＝
  ( comp-hom-simplex-Category {n} {r} {s}
    ( h)
    ( comp-hom-simplex-Category {n} {m} {r} g f))
associative-comp-hom-simplex-Category {n} {m} {r} {s} =
  associative-comp-hom-Poset
    ( Fin-Poset (succ-ℕ n))
    ( Fin-Poset (succ-ℕ m))
    ( Fin-Poset (succ-ℕ r))
    ( Fin-Poset (succ-ℕ s))

associative-composition-structure-simplex-Category :
  associative-composition-structure-Set hom-set-simplex-Category
pr1 associative-composition-structure-simplex-Category {n} {m} {r} =
  comp-hom-simplex-Category {n} {m} {r}
pr2 associative-composition-structure-simplex-Category {n} {m} {r} {s} =
  associative-comp-hom-simplex-Category {n} {m} {r} {s}

id-hom-simplex-Category : (n : obj-simplex-Category) → hom-simplex-Category n n
id-hom-simplex-Category n = id-hom-Poset (Fin-Poset (succ-ℕ n))

left-unit-law-comp-hom-simplex-Category :
  {n m : obj-simplex-Category} (f : hom-simplex-Category n m) →
  comp-hom-simplex-Category {n} {m} {m} (id-hom-simplex-Category m) f ＝ f
left-unit-law-comp-hom-simplex-Category {n} {m} =
  left-unit-law-comp-hom-Poset (Fin-Poset (succ-ℕ n)) (Fin-Poset (succ-ℕ m))

right-unit-law-comp-hom-simplex-Category :
  {n m : obj-simplex-Category} (f : hom-simplex-Category n m) →
  comp-hom-simplex-Category {n} {n} {m} f (id-hom-simplex-Category n) ＝ f
right-unit-law-comp-hom-simplex-Category {n} {m} =
  right-unit-law-comp-hom-Poset (Fin-Poset (succ-ℕ n)) (Fin-Poset (succ-ℕ m))

is-unital-composition-structure-simplex-Category :
  is-unital-composition-structure-Set
    ( hom-set-simplex-Category)
    ( associative-composition-structure-simplex-Category)
pr1 is-unital-composition-structure-simplex-Category = id-hom-simplex-Category
pr1 (pr2 is-unital-composition-structure-simplex-Category) {n} {m} =
  left-unit-law-comp-hom-simplex-Category {n} {m}
pr2 (pr2 is-unital-composition-structure-simplex-Category) {n} {m} =
  right-unit-law-comp-hom-simplex-Category {n} {m}

simplex-Precategory : Precategory lzero lzero
pr1 simplex-Precategory = obj-simplex-Category
pr1 (pr2 simplex-Precategory) = hom-set-simplex-Category
pr1 (pr2 (pr2 simplex-Precategory)) =
  associative-composition-structure-simplex-Category
pr2 (pr2 (pr2 simplex-Precategory)) =
  is-unital-composition-structure-simplex-Category
```

### The simplex category

It remains to be formalized that the simplex category is univalent.

## Properties

### The simplex category has a face map and degeneracy unique factorization system

This remains to be formalized.

### The simplex category has a degeneracy and face map unique factorization system

This remains to be formalized.

### There is a unique non-trivial involution on the simplex category

This remains to be formalized.
