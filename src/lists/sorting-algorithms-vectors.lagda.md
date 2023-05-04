# Sorting algorithms for vectors

```agda
module lists.sorting-algorithms-vectors where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import finite-group-theory.permutations-standard-finite-types

open import foundation.cartesian-product-types
open import foundation.universe-levels

open import linear-algebra.vectors

open import lists.permutation-vectors
open import lists.sorted-vectors

open import order-theory.total-decidable-posets

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
  {l1 l2 : Level} (X : total-Decidable-Poset l1 l2)
  where

  is-sort-vec :
    (f :
      {n : ℕ} →
      vec (element-total-Decidable-Poset X) n →
      vec (element-total-Decidable-Poset X) n) →
    UU (l1 ⊔ l2)
  is-sort-vec f =
    (n : ℕ) →
    is-permutation-vec n f ×
    ((v : vec (element-total-Decidable-Poset X) n) → is-sorted-vec X (f v))
```
