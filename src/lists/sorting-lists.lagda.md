# Sorting of lists

```agda
module lists.sorting-lists where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.strong-induction-natural-numbers

open import foundation.universe-levels
open import foundation.propositions
open import foundation.unit-type
open import foundation.empty-types
open import foundation.cartesian-product-types
open import foundation.coproduct-types
open import foundation.functoriality-coproduct-types
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.functions
open import foundation.equivalences

open import univalent-combinatorics.standard-finite-types
open import univalent-combinatorics.permutations-standard-finite-types

open import lists.lists
open import lists.arrays
open import lists.concatenation-lists

open import linear-algebra.vectors

open import order-theory.total-decidable-posets
```

</details>

## Idea

In these file, we define sorted lists, sorted vectors and sorted arrays.

## Definitions

### Lists

```agda
module _
  {l1 l2 : Level} (X : total-decidable-Poset l1 l2)
  where

  is-sorted-list-Prop : list (element-total-decidable-Poset X) → Prop l2
  is-sorted-list-Prop nil = raise-unit-Prop l2
  is-sorted-list-Prop (cons x nil) = raise-unit-Prop l2
  is-sorted-list-Prop (cons x (cons y l)) =
    prod-Prop
      ( leq-total-decidable-poset-Prop X x y)
      ( is-sorted-list-Prop (cons y l))

  is-sorted-list : list (element-total-decidable-Poset X) → UU l2
  is-sorted-list l = type-Prop (is-sorted-list-Prop l)
```

### Vectors

```agda
module _
  {l1 l2 : Level} (X : total-decidable-Poset l1 l2)
  where

  is-leq-all-element-vec-Prop :
    {n : ℕ} → element-total-decidable-Poset X →
    vec (element-total-decidable-Poset X) n → Prop l2
  is-leq-all-element-vec-Prop {zero-ℕ} x v = raise-unit-Prop l2
  is-leq-all-element-vec-Prop {succ-ℕ n} x (y ∷ v) =
    prod-Prop
      ( leq-total-decidable-poset-Prop X x y)
      ( is-leq-all-element-vec-Prop x v)


  is-leq-all-element-vec :
    {n : ℕ} → element-total-decidable-Poset X →
    vec (element-total-decidable-Poset X) n → UU l2
  is-leq-all-element-vec x v = type-Prop (is-leq-all-element-vec-Prop x v)

  is-sorted-vec-Prop : {n : ℕ} → vec (element-total-decidable-Poset X) n → Prop l2
  is-sorted-vec-Prop {zero-ℕ} l = raise-unit-Prop l2
  is-sorted-vec-Prop {1} (x ∷ l) = raise-unit-Prop l2
  is-sorted-vec-Prop {succ-ℕ (succ-ℕ n)} (x ∷ y ∷ l) =
    prod-Prop
      ( leq-total-decidable-poset-Prop X x y)
      ( is-sorted-vec-Prop (y ∷ l))

  is-sorted-vec :
    {n : ℕ} → vec (element-total-decidable-Poset X) n → UU l2
  is-sorted-vec l = type-Prop (is-sorted-vec-Prop l)
```

### Arrays

```agda

```

## Properties

### Vectors

#### If a vector is sorted, then its tail is also sorted.

```agda
  is-sorted-tail-is-sorted-vec :
    {n : ℕ} → (v : vec (element-total-decidable-Poset X) (succ-ℕ n)) →
    is-sorted-vec v → is-sorted-vec (tail-vec v)
  is-sorted-tail-is-sorted-vec {zero-ℕ} (x ∷ empty-vec) s = raise-star
  is-sorted-tail-is-sorted-vec {succ-ℕ n} (x ∷ y ∷ v) s = pr2 s

  is-leq-head-head-tail-is-sorted-vec :
    {n : ℕ} → (v : vec (element-total-decidable-Poset X) (succ-ℕ (succ-ℕ n))) →
    is-sorted-vec v → leq-total-decidable-Poset X (head-vec v) (head-vec (tail-vec v))
  is-leq-head-head-tail-is-sorted-vec (x ∷ y ∷ v) s = pr1 s
```

#### If a vector `v' ＝ y ∷ v` is sorted then for all element `x` less or equal than `y`, `x` is less or equal than every element in the vector.

```agda
  is-leq-all-element-vec-is-leq-head-sorted-vec :
    {n : ℕ}
    (x : element-total-decidable-Poset X)
    (v : vec (element-total-decidable-Poset X) (succ-ℕ n)) →
    is-sorted-vec v → leq-total-decidable-Poset X x (head-vec v) →
    is-leq-all-element-vec x v
  is-leq-all-element-vec-is-leq-head-sorted-vec {zero-ℕ} x (y ∷ v) s p =
    p , raise-star
  is-leq-all-element-vec-is-leq-head-sorted-vec {succ-ℕ n} x (y ∷ v) s p =
    p ,
    ( is-leq-all-element-vec-is-leq-head-sorted-vec
        ( x)
        ( v)
        ( is-sorted-tail-is-sorted-vec (y ∷ v) s)
        ( transitive-leq-total-decidable-Poset
            ( X)
            ( x)
            ( y)
            ( head-vec v)
            ( is-leq-head-head-tail-is-sorted-vec (y ∷ v) s)
            ( p)))
```

#### If the tail of a vector `v' ＝ x ∷ y ∷ v` is sorted and `x ≤ y`, then `v'` is sorted

```agda
  is-sorted-vec-is-sorted-tail-is-leq-head-vec :
    {n : ℕ}
    (v : vec (element-total-decidable-Poset X) (succ-ℕ (succ-ℕ n))) →
    is-sorted-vec (tail-vec v) →
    (leq-total-decidable-Poset X (head-vec v) (head-vec (tail-vec v))) →
    is-sorted-vec v
  is-sorted-vec-is-sorted-tail-is-leq-head-vec (x ∷ y ∷ v) s p = p , s
```
