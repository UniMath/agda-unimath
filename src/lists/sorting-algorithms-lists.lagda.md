# Sorting algorithms for lists

```agda
module lists.sorting-algorithms-lists where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import finite-group-theory.permutations-standard-finite-types

open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.universe-levels

open import lists.arrays
open import lists.lists
open import lists.permutation-lists
open import lists.sorted-lists
open import lists.sorting-algorithms-tuples
open import lists.tuples

open import order-theory.decidable-total-orders
```

</details>

## Idea

In this file we define the notion of sorting algorithms for lists.

## Definition

A function `f` from `list` to `list` is a sort if `f` is a permutation and if
for every list `l`, `f l` is sorted

```agda
module _
  {l1 l2 : Level}
  (X : Decidable-Total-Order l1 l2)
  (f :
      list (type-Decidable-Total-Order X) →
      list (type-Decidable-Total-Order X))
  where

  is-sort-list : UU (l1 ⊔ l2)
  is-sort-list =
    is-permutation-list f ×
    ((l : list (type-Decidable-Total-Order X)) → is-sorted-list X (f l))

  is-permutation-list-is-sort-list :
    is-sort-list → is-permutation-list f
  is-permutation-list-is-sort-list S = pr1 (S)

  permutation-list-is-sort-list :
    is-sort-list → (l : list (type-Decidable-Total-Order X)) →
    Permutation (length-list l)
  permutation-list-is-sort-list S l =
    permutation-is-permutation-list f (is-permutation-list-is-sort-list S) l

  eq-permute-list-permutation-is-sort-list :
    (S : is-sort-list) (l : list (type-Decidable-Total-Order X)) →
    f l ＝ permute-list l (permutation-list-is-sort-list S l)
  eq-permute-list-permutation-is-sort-list S l =
    eq-permute-list-permutation-is-permutation-list
      ( f)
      ( is-permutation-list-is-sort-list S) l

  is-sorting-list-is-sort-list :
    is-sort-list →
    (l : list (type-Decidable-Total-Order X)) → is-sorted-list X (f l)
  is-sorting-list-is-sort-list S = pr2 (S)
```

## Properties

### From sorting algorithms for tuples to sorting algorithms for lists

```agda
module _
  {l1 l2 : Level}
  (X : Decidable-Total-Order l1 l2)
  where

  is-sort-list-is-sort-tuple :
    (f :
      {n : ℕ} →
      tuple (type-Decidable-Total-Order X) n →
      tuple (type-Decidable-Total-Order X) n) →
    is-sort-tuple X f →
    is-sort-list X (λ l → list-tuple (length-list l) (f (tuple-list l)))
  pr1 (is-sort-list-is-sort-tuple f S) =
    is-permutation-list-is-permutation-tuple
      ( λ n → f)
      ( λ n → pr1 (S n))
  pr2 (is-sort-list-is-sort-tuple f S) l =
    is-sorted-list-is-sorted-tuple
      ( X)
      ( length-list l)
      ( f (tuple-list l)) (pr2 (S (length-list l)) (tuple-list l))
```
