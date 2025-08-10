# Sorting algorithms for tuples

```agda
module lists.sorting-algorithms-tuples where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import finite-group-theory.permutations-standard-finite-types

open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.universe-levels

open import lists.permutation-tuples
open import lists.sorted-tuples
open import lists.tuples

open import order-theory.decidable-total-orders
```

</details>

## Idea

A function `f` on tuples is a **sort** if `f` is a permutation and if for every
tuple `v`, `f v` is sorted.

## Definition

```agda
module _
  {l1 l2 : Level}
  (X : Decidable-Total-Order l1 l2)
  (f :
      {n : ℕ} →
      tuple (type-Decidable-Total-Order X) n →
      tuple (type-Decidable-Total-Order X) n)
  where

  is-sort-tuple :
    UU (l1 ⊔ l2)
  is-sort-tuple =
    (n : ℕ) →
    is-permutation-tuple n f ×
    ((v : tuple (type-Decidable-Total-Order X) n) → is-sorted-tuple X (f v))

  is-permutation-tuple-is-sort-tuple :
    is-sort-tuple → (n : ℕ) → is-permutation-tuple n f
  is-permutation-tuple-is-sort-tuple S n = pr1 (S n)

  permutation-tuple-is-sort-tuple :
    is-sort-tuple → (n : ℕ) → tuple (type-Decidable-Total-Order X) n →
    Permutation n
  permutation-tuple-is-sort-tuple S n v =
    permutation-is-permutation-tuple
      ( n)
      ( f)
      ( is-permutation-tuple-is-sort-tuple S n)
      ( v)

  eq-permute-tuple-permutation-is-sort-tuple :
    (S : is-sort-tuple) (n : ℕ) (v : tuple (type-Decidable-Total-Order X) n) →
    f v ＝ permute-tuple n v (permutation-tuple-is-sort-tuple S n v)
  eq-permute-tuple-permutation-is-sort-tuple S n v =
    eq-permute-tuple-permutation-is-permutation-tuple
      ( n)
      ( f)
      ( is-permutation-tuple-is-sort-tuple S n) v

  is-sorting-tuple-is-sort-tuple :
    is-sort-tuple → (n : ℕ) →
    (v : tuple (type-Decidable-Total-Order X) n) → is-sorted-tuple X (f v)
  is-sorting-tuple-is-sort-tuple S n = pr2 (S n)
```
