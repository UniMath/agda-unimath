# Cycle prime decompositions of natural numbers

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module univalent-combinatorics.cycle-prime-decomposition-natural-numbers
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.decidable-total-order-natural-numbers funext univalence truncations
open import elementary-number-theory.fundamental-theorem-of-arithmetic funext univalence truncations
open import elementary-number-theory.inequality-natural-numbers funext univalence truncations
open import elementary-number-theory.multiplication-natural-numbers
open import elementary-number-theory.natural-numbers

open import finite-group-theory.permutations-standard-finite-types funext univalence truncations

open import foundation.action-on-identifications-functions
open import foundation.cartesian-product-types funext univalence
open import foundation.contractible-types funext univalence
open import foundation.dependent-pair-types
open import foundation.dependent-products-contractible-types funext
open import foundation.equivalences funext
open import foundation.identity-types funext
open import foundation.iterated-cartesian-product-types funext univalence truncations
open import foundation.transport-along-identifications
open import foundation.univalence funext univalence
open import foundation.universe-levels

open import group-theory.concrete-groups funext univalence truncations
open import group-theory.iterated-cartesian-products-concrete-groups funext univalence truncations

open import lists.arrays funext univalence truncations
open import lists.concatenation-lists funext univalence truncations
open import lists.functoriality-lists funext univalence truncations
open import lists.permutation-lists funext univalence truncations
open import lists.sort-by-insertion-lists funext univalence truncations

open import univalent-combinatorics.cyclic-finite-types funext univalence truncations
```

</details>

## Idea

Let `n` be a natural number. The `cycle-prime-decomposition-ℕ` of `n` is the
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

### Cycle prime decomposition are closed under cartesian products

The cartesian product of the cycle prime decomposition of `n` and `m` is equal
to the cycle prime decomposition of `n *ℕ m`.

```agda
equiv-product-cycle-prime-decomposition-ℕ :
  (n m : ℕ) → (H : leq-ℕ 1 n) → (I : leq-ℕ 1 m) →
  ( cycle-prime-decomposition-ℕ n H × cycle-prime-decomposition-ℕ m I) ≃
  cycle-prime-decomposition-ℕ (n *ℕ m) (preserves-leq-mul-ℕ 1 n 1 m H I)
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
                ( n *ℕ m)
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
                (n *ℕ m)
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
              ( list-fundamental-theorem-arithmetic-ℕ m I))))) ∘e
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
