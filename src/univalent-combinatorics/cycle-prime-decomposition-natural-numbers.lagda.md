# Cycle decompositions of a natural numbers

```agda
module univalent-combinatorics.cycle-prime-decomposition-natural-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.fundamental-theorem-of-arithmetic
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.iterated-cartesian-product-types
open import foundation.universe-levels

open import group-theory.concrete-groups
open import group-theory.iterated-cartesian-products-concrete-groups

open import lists.arrays
open import lists.functoriality-lists

open import univalent-combinatorics.cyclic-types
```

</details>

## Idea

Let `n` be a natural numbers. The `cycle-prime-decomposition-ℕ` of `n` is the
iterated cartesian product of the cyclic types assocated to the prime
decomposition of `n`.

## Definition

```agda
concrete-group-cycle-prime-decomposition-ℕ :
  (n : ℕ) → leq-ℕ 1 n → Concrete-Group (lsuc lzero)
concrete-group-cycle-prime-decomposition-ℕ n H =
  iterated-product-Concrete-Group
    ( length-array
      ( array-list
        ( map-list
          ( concrete-group-Cyclic-Type)
          ( list-fundamental-theorem-arithmetic-ℕ n H))))
    ( functional-vec-array
      ( array-list
        ( map-list
          ( concrete-group-Cyclic-Type)
          ( list-fundamental-theorem-arithmetic-ℕ n H))))

cycle-prime-decomposition-ℕ :
  (n : ℕ) → leq-ℕ 1 n → UU (lsuc lzero)
cycle-prime-decomposition-ℕ n H =
  iterated-product-lists
    ( map-list (Cyclic-Type lzero) (list-fundamental-theorem-arithmetic-ℕ n H))
```
