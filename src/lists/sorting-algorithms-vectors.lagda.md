# Sorting algorithms for vectors

```agda
module lists.sorting-algorithms-vectors where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.strong-induction-natural-numbers

open import foundation.cartesian-product-types
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.equivalences
open import foundation.functions
open import foundation.functoriality-coproduct-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.unit-type
open import foundation.universe-levels

open import linear-algebra.vectors

open import lists.arrays
open import lists.concatenation-lists
open import lists.lists
open import lists.permutation-lists
open import lists.sorted-vectors

open import order-theory.total-decidable-posets

open import univalent-combinatorics.permutations-standard-finite-types
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

In these file we define the notion of sorting algorithms.

## Definition

A function `f` from `vec` to `vec` is a sort if `f` is a permutation and if for
every vector `v`, `f v` is sorted

```agda
module _
  {l1 l2 : Level} (X : total-decidable-Poset l1 l2)
  where

  is-a-sort-vec :
    (f :
      {n : ℕ} →
      vec (element-total-decidable-Poset X) n →
      vec (element-total-decidable-Poset X) n) →
    UU (l1 ⊔ l2)
  is-a-sort-vec f =
    (n : ℕ) →
    is-permutation-vec n f ×
    ((v : vec (element-total-decidable-Poset X) n) → is-sorted-vec X (f v))
```
