# Counting permutations of standard finite types

```agda
{-# OPTIONS --lossy-unification #-}

module finite-group-theory.counting-permutations-standard-finite-types where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.factorials
open import elementary-number-theory.natural-numbers

open import finite-group-theory.permutations-standard-finite-types

open import foundation.automorphisms
open import foundation.automorphisms-discrete-types
open import foundation.cartesian-product-types
open import foundation.contractible-types
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.equivalences
open import foundation.equivalences-contractible-types
open import foundation.function-types
open import foundation.functoriality-cartesian-product-types
open import foundation.identity-types
open import foundation.unit-type
open import foundation.universe-levels

open import univalent-combinatorics.cartesian-product-types
open import univalent-combinatorics.counting
open import univalent-combinatorics.equality-standard-finite-types
open import univalent-combinatorics.finite-types
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

The [permutations](finite-group-theory.permutations-standard-finite-types.md) of
the [standard finite type](univalent-combinatorics.standard-finite-types.md)
with `n` elements are a [finite type](univalent-combinatorics.finite-types.md)
with `n` [factorial](elementary-number-theory.factorials.md) elements.

## Proof

### `Permutation (n + 1) ≃ Permutation n × Fin (n + 1)`

```agda
module _
  (n : ℕ)
  where

  compute-Permutation-succ-ℕ :
    Permutation (succ-ℕ n) ≃ Permutation n × Fin (succ-ℕ n)
  compute-Permutation-succ-ℕ =
    equiv-product
      ( conjugation-aut (compute-complement-neg-one-Fin n))
      ( id-equiv) ∘e
    compute-aut-Discrete-Type (Fin-Discrete-Type (succ-ℕ n)) (inr star)
```

### Counting the elements of `Permutation n`

```agda
is-contr-Permutation-0 : is-contr (Permutation 0)
is-contr-Permutation-0 = is-contr-equiv-is-empty id id

equiv-count-Permutation :
  (n : ℕ) → Fin (factorial-ℕ n) ≃ Permutation n
equiv-count-Permutation zero-ℕ =
  equiv-is-contr is-contr-Fin-1 is-contr-Permutation-0
equiv-count-Permutation (succ-ℕ n) =
  inv-equiv (compute-Permutation-succ-ℕ n) ∘e
  equiv-product (equiv-count-Permutation n) id-equiv ∘e
  inv-equiv (product-Fin (factorial-ℕ n) (succ-ℕ n))

count-Permutation : (n : ℕ) → count (Permutation n)
pr1 (count-Permutation n) = factorial-ℕ n
pr2 (count-Permutation n) = equiv-count-Permutation n
```

### `Permutation n` is finite

```agda
finite-type-Permutation : (n : ℕ) → Finite-Type lzero
finite-type-Permutation n =
  ( Permutation n , is-finite-count (count-Permutation n))
```

### The number of elements of `Permutation n` is n

```agda
abstract
  number-of-elements-count-Permutation :
    (n : ℕ) →
    number-of-elements-count (count-Permutation n) ＝ factorial-ℕ n
  number-of-elements-count-Permutation n = refl

  number-of-elements-Permutation :
    (n : ℕ) →
    number-of-elements-Finite-Type (finite-type-Permutation n) ＝ factorial-ℕ n
  number-of-elements-Permutation n =
    inv (compute-number-of-elements-is-finite (count-Permutation n) _)
```
