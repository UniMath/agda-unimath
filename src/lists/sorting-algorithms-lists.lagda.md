# Sorting algorithms for lists

```agda
module lists.sorting-algorithms-lists where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import finite-group-theory.permutations-standard-finite-types

open import foundation.cartesian-product-types
open import foundation.universe-levels
open import foundation.dependent-pair-types

open import linear-algebra.vectors

open import lists.permutation-lists
open import lists.sorted-lists
open import lists.lists
open import lists.sorting-algorithms-vectors
open import lists.arrays

open import order-theory.decidable-total-orders

open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

In these file we define the notion of sorting algorithms.

## Definition

A function `f` from `list` to `list` is a sort if `f` is a permutation and if for
every list `l`, `f l` is sorted

```agda
module _
  {l1 l2 : Level} (X : Decidable-Total-Order l1 l2)
  where

  is-sort-list :
    (f :
      list (type-Decidable-Total-Order X) →
      list (type-Decidable-Total-Order X)) →
    UU (l1 ⊔ l2)
  is-sort-list f =
    is-permutation-list f ×
    ((l : list (type-Decidable-Total-Order X)) → is-sorted-list X (f l))
```

## Properties

### From sorting algorithms for vectors to sorting algorithms for lists

```agda
  is-sort-list-is-sort-vec :
    (f :
      {n : ℕ} →
      vec (type-Decidable-Total-Order X) n →
      vec (type-Decidable-Total-Order X) n) →
    is-sort-vec X f →
    is-sort-list (λ l → list-vec (length-list l) (f (vec-list l)))
  pr1 (is-sort-list-is-sort-vec f S) =
    is-permutation-list-is-permutation-vec
      ( λ n → f)
      ( λ n → pr1 (S n))
  pr2 (is-sort-list-is-sort-vec f S) l =
    is-sorted-list-is-sorted-vec
      ( X)
      ( length-list l)
      ( f (vec-list l)) (pr2 (S (length-list l) ) (vec-list l))
```
