# The augmented simplex category

```agda
module category-theory.augmented-simplex-category where
```

<details><summary>Imports</summary>

```agda
open import category-theory.composition-operations-on-binary-families-of-sets
open import category-theory.precategories

open import elementary-number-theory.inequality-standard-finite-types
open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.sets
open import foundation.strictly-involutive-identity-types
open import foundation.universe-levels

open import order-theory.order-preserving-maps-posets
```

</details>

## Idea

**The augmented simplex category** is the category consisting of
[finite total orders](order-theory.finite-total-orders.md) and
[order-preserving maps](order-theory.order-preserving-maps-posets.md). However,
we define it as the category whose objects are
[natural numbers](elementary-number-theory.natural-numbers.md) and whose
hom-[sets](foundation-core.sets.md) `hom n m` are order-preserving maps between
the [standard finite types](univalent-combinatorics.standard-finite-types.md)
`Fin n` to `Fin m` [equipped](foundation.structure.md) with the
[standard ordering](elementary-number-theory.inequality-standard-finite-types.md),
and then show that it is
[equivalent](category-theory.equivalences-of-precategories.md) to the former.

## Definition

### The augmented simplex precategory

```agda
obj-augmented-simplex-Category : UU lzero
obj-augmented-simplex-Category = ℕ

hom-set-augmented-simplex-Category :
  obj-augmented-simplex-Category → obj-augmented-simplex-Category → Set lzero
hom-set-augmented-simplex-Category n m =
  hom-set-Poset (Fin-Poset n) (Fin-Poset m)

hom-augmented-simplex-Category :
  obj-augmented-simplex-Category → obj-augmented-simplex-Category → UU lzero
hom-augmented-simplex-Category n m =
  type-Set (hom-set-augmented-simplex-Category n m)

comp-hom-augmented-simplex-Category :
  {n m r : obj-augmented-simplex-Category} →
  hom-augmented-simplex-Category m r →
  hom-augmented-simplex-Category n m →
  hom-augmented-simplex-Category n r
comp-hom-augmented-simplex-Category {n} {m} {r} =
  comp-hom-Poset (Fin-Poset n) (Fin-Poset m) (Fin-Poset r)

associative-comp-hom-augmented-simplex-Category :
  {n m r s : obj-augmented-simplex-Category}
  (h : hom-augmented-simplex-Category r s)
  (g : hom-augmented-simplex-Category m r)
  (f : hom-augmented-simplex-Category n m) →
  comp-hom-augmented-simplex-Category {n} {m} {s}
    ( comp-hom-augmented-simplex-Category {m} {r} {s} h g)
    ( f) ＝
  comp-hom-augmented-simplex-Category {n} {r} {s}
    ( h)
    ( comp-hom-augmented-simplex-Category {n} {m} {r} g f)
associative-comp-hom-augmented-simplex-Category {n} {m} {r} {s} =
  associative-comp-hom-Poset
    ( Fin-Poset n)
    ( Fin-Poset m)
    ( Fin-Poset r)
    ( Fin-Poset s)

involutive-eq-associative-comp-hom-augmented-simplex-Category :
  {n m r s : obj-augmented-simplex-Category}
  (h : hom-augmented-simplex-Category r s)
  (g : hom-augmented-simplex-Category m r)
  (f : hom-augmented-simplex-Category n m) →
  comp-hom-augmented-simplex-Category {n} {m} {s}
    ( comp-hom-augmented-simplex-Category {m} {r} {s} h g)
    ( f) ＝ⁱ
  comp-hom-augmented-simplex-Category {n} {r} {s}
    ( h)
    ( comp-hom-augmented-simplex-Category {n} {m} {r} g f)
involutive-eq-associative-comp-hom-augmented-simplex-Category {n} {m} {r} {s} =
  involutive-eq-associative-comp-hom-Poset
    ( Fin-Poset n)
    ( Fin-Poset m)
    ( Fin-Poset r)
    ( Fin-Poset s)

associative-composition-operation-augmented-simplex-Category :
  associative-composition-operation-binary-family-Set
    hom-set-augmented-simplex-Category
pr1 associative-composition-operation-augmented-simplex-Category {n} {m} {r} =
  comp-hom-augmented-simplex-Category {n} {m} {r}
pr2 associative-composition-operation-augmented-simplex-Category
  { n} {m} {r} {s} =
  involutive-eq-associative-comp-hom-augmented-simplex-Category {n} {m} {r} {s}

id-hom-augmented-simplex-Category :
  (n : obj-augmented-simplex-Category) → hom-augmented-simplex-Category n n
id-hom-augmented-simplex-Category n = id-hom-Poset (Fin-Poset n)

left-unit-law-comp-hom-augmented-simplex-Category :
  {n m : obj-augmented-simplex-Category}
  (f : hom-augmented-simplex-Category n m) →
  comp-hom-augmented-simplex-Category {n} {m} {m}
    ( id-hom-augmented-simplex-Category m)
    ( f) ＝
  f
left-unit-law-comp-hom-augmented-simplex-Category {n} {m} =
  left-unit-law-comp-hom-Poset (Fin-Poset n) (Fin-Poset m)

right-unit-law-comp-hom-augmented-simplex-Category :
  {n m : obj-augmented-simplex-Category}
  (f : hom-augmented-simplex-Category n m) →
  comp-hom-augmented-simplex-Category {n} {n} {m}
    ( f)
    ( id-hom-augmented-simplex-Category n) ＝
  f
right-unit-law-comp-hom-augmented-simplex-Category {n} {m} =
  right-unit-law-comp-hom-Poset (Fin-Poset n) (Fin-Poset m)

is-unital-composition-operation-augmented-simplex-Category :
  is-unital-composition-operation-binary-family-Set
    ( hom-set-augmented-simplex-Category)
    ( λ {n} {m} {r} → comp-hom-augmented-simplex-Category {n} {m} {r})
pr1 is-unital-composition-operation-augmented-simplex-Category =
  id-hom-augmented-simplex-Category
pr1 (pr2 is-unital-composition-operation-augmented-simplex-Category) {n} {m} =
  left-unit-law-comp-hom-augmented-simplex-Category {n} {m}
pr2 (pr2 is-unital-composition-operation-augmented-simplex-Category) {n} {m} =
  right-unit-law-comp-hom-augmented-simplex-Category {n} {m}

augmented-simplex-Precategory : Precategory lzero lzero
pr1 augmented-simplex-Precategory = obj-augmented-simplex-Category
pr1 (pr2 augmented-simplex-Precategory) = hom-set-augmented-simplex-Category
pr1 (pr2 (pr2 augmented-simplex-Precategory)) =
  associative-composition-operation-augmented-simplex-Category
pr2 (pr2 (pr2 augmented-simplex-Precategory)) =
  is-unital-composition-operation-augmented-simplex-Category
```

### The augmented simplex category

It remains to be formalized that the augmented simplex category is univalent.

## Properties

### The augmented simplex category is equivalent to the category of finite total orders

This remains to be formalized.
