# Sort by insertion for lists

```agda
module lists.sort-by-insertion-lists where
```

<details><summary>Imports</summary>

```agda
open import finite-group-theory.permutations-standard-finite-types

open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.universe-levels

open import lists.arrays
open import lists.lists
open import lists.permutation-lists
open import lists.sort-by-insertion-tuples
open import lists.sorted-lists
open import lists.sorting-algorithms-lists

open import order-theory.decidable-total-orders
```

</details>

## Idea

{{#concept "Sort by insertion" Disambiguation="for lists" WD="insertion sort" WDID=Q117241 Agda=insertion-sort-list}}
is a recursive [sorting algorithm](lists.sorting-algorithms-lists.md) on
[lists](lists.lists.md). If a list is empty or with only one element then it is
sorted. Otherwise, we recursively sort the tail of the list. Then we compare the
head of the list to the head of the [sorted](lists.sorted-lists.md) tail. If the
head is less or equal than the head of the tail the list is sorted. Otherwise we
permute the two elements and we recursively sort the tail of the list.

We use the definition of
[sort by insertion for tuples](lists.sort-by-insertion-tuples.md) and adapt it
for lists.

## Definition

```agda
module _
  {l1 l2 : Level} (X : Decidable-Total-Order l1 l2)
  where

  insertion-sort-list :
    list (type-Decidable-Total-Order X) → list (type-Decidable-Total-Order X)
  insertion-sort-list l =
    list-tuple (length-list l) (insertion-sort-tuple X (tuple-list l))
```

## Properties

### Sort by insertion is a sort

```agda
  is-sort-insertion-sort-list :
    is-sort-list X insertion-sort-list
  is-sort-insertion-sort-list =
    is-sort-list-is-sort-tuple
      ( X)
      ( insertion-sort-tuple X)
      ( is-sort-insertion-sort-tuple X)

  is-permutation-insertion-sort-list : is-permutation-list insertion-sort-list
  is-permutation-insertion-sort-list = pr1 (is-sort-insertion-sort-list)

  permutation-insertion-sort-list :
    (l : list (type-Decidable-Total-Order X)) →
    Permutation (length-list l)
  permutation-insertion-sort-list =
    permutation-list-is-sort-list
      X
      insertion-sort-list
      is-sort-insertion-sort-list

  eq-permute-list-permutation-insertion-sort-list :
    (l : list (type-Decidable-Total-Order X)) →
    insertion-sort-list l ＝ permute-list l (permutation-insertion-sort-list l)
  eq-permute-list-permutation-insertion-sort-list =
    eq-permute-list-permutation-is-sort-list
      X
      insertion-sort-list
      is-sort-insertion-sort-list

  is-sorting-insertion-sort-list :
    (l : list (type-Decidable-Total-Order X)) →
    is-sorted-list X (insertion-sort-list l)
  is-sorting-insertion-sort-list = pr2 (is-sort-insertion-sort-list)
```
