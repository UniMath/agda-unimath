# Cycle decompositions of a natural numbers

```agda
module univalent-combinatorics.cycle-prime-decomposition-natural-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.fundamental-theorem-of-arithmetic
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.multiplication-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.decidable-total-order-natural-numbers

open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.identity-types
open import foundation.iterated-cartesian-product-types
open import foundation.universe-levels
open import foundation.univalence
open import foundation.contractible-types

open import group-theory.concrete-groups
open import group-theory.iterated-cartesian-products-concrete-groups

open import lists.arrays
open import lists.functoriality-lists
open import lists.lists
open import lists.concatenation-lists
open import lists.sort-by-insertion-lists
open import lists.permutation-lists

open import univalent-combinatorics.cyclic-types
open import univalent-combinatorics.finite-types

open import finite-group-theory.permutations-standard-finite-types
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

## Properties

### Cycle prime decomposition is closed by cartesian product

The cartesian product of the cycle prime decomposition of `n` and `m` is equal
to the cycle prime decomposition of `mul-ℕ n m`

```agda
equiv-product-cycle-prime-decomposition-ℕ :
  (n m : ℕ) → (H : leq-ℕ 1 n) → (I : leq-ℕ 1 m) →
  ( cycle-prime-decomposition-ℕ n H × cycle-prime-decomposition-ℕ m I) ≃
  cycle-prime-decomposition-ℕ (mul-ℕ n m) (preserves-leq-mul-ℕ 1 n 1 m H I)
equiv-product-cycle-prime-decomposition-ℕ n m H I =
  ( ( equiv-eq
      ( ap
        ( λ p → iterated-product-lists (map-list (Cyclic-Type lzero) p))
        ( ( inv
            ( eq-permute-list-permutation-insertion-sort-list
              ( ℕ-Decidable-Total-Order)
              ( concat-list
                ( list-fundamental-theorem-arithmetic-ℕ n H)
                ( list-fundamental-theorem-arithmetic-ℕ m I)))) ∙
          ( ap
            ( pr1)
            ( eq-is-contr'
              ( fundamental-theorem-arithmetic-list-ℕ
                ( mul-ℕ n m)
                ( preserves-leq-mul-ℕ 1 n 1 m H I))
              ( prime-decomposition-list-sort-concatenation-ℕ
                ( n)
                ( m)
                ( H)
                ( I)
                ( list-fundamental-theorem-arithmetic-ℕ n H)
                ( list-fundamental-theorem-arithmetic-ℕ m I)
                ( is-prime-decomposition-list-fundamental-theorem-arithmetic-ℕ
                  n
                  H)
                ( is-prime-decomposition-list-fundamental-theorem-arithmetic-ℕ
                  m
                  I))
              ( prime-decomposition-fundamental-theorem-arithmetic-list-ℕ
                ( mul-ℕ n m)
                ( preserves-leq-mul-ℕ 1 n 1 m H I))))))) ∘e
    ( equiv-eq
      ( ap
        ( iterated-product-lists)
        ( eq-map-list-permute-list
          ( Cyclic-Type lzero)
          ( concat-list
            ( list-fundamental-theorem-arithmetic-ℕ n H)
            ( list-fundamental-theorem-arithmetic-ℕ m I))
          ( permutation-insertion-sort-list
            ( ℕ-Decidable-Total-Order)
            ( concat-list
              ( list-fundamental-theorem-arithmetic-ℕ n H)
              ( list-fundamental-theorem-arithmetic-ℕ m I)))))  ∘e
      ( ( inv-equiv
           ( equiv-permutation-iterated-product-lists
             ( map-list
               ( Cyclic-Type lzero)
               ( concat-list
                 ( list-fundamental-theorem-arithmetic-ℕ n H)
                 ( list-fundamental-theorem-arithmetic-ℕ m I)))
             ( tr
               ( Permutation)
               ( inv
                 ( length-map-list
                   ( Cyclic-Type lzero)
                   ( concat-list
                     ( list-fundamental-theorem-arithmetic-ℕ n H)
                     ( list-fundamental-theorem-arithmetic-ℕ m I))))
               ( permutation-insertion-sort-list
                 ( ℕ-Decidable-Total-Order)
                 ( concat-list
                   ( list-fundamental-theorem-arithmetic-ℕ n H)
                   ( list-fundamental-theorem-arithmetic-ℕ m I)))))) ∘e
        ( ( equiv-eq
            ( ap
              ( iterated-product-lists)
              ( inv
                ( preserves-concat-map-list
                  ( Cyclic-Type lzero)
                  ( list-fundamental-theorem-arithmetic-ℕ n H)
                  ( list-fundamental-theorem-arithmetic-ℕ m I))))) ∘e
          ( equiv-product-iterated-product-lists
            ( map-list
              ( Cyclic-Type lzero)
              ( list-fundamental-theorem-arithmetic-ℕ n H))
            ( map-list
              ( Cyclic-Type lzero)
              ( list-fundamental-theorem-arithmetic-ℕ m I)))))))
```
