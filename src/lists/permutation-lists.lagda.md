# Permutations of lists and arrays

```agda
module lists.permutation-lists where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.universe-levels
open import foundation.dependent-pair-types
open import foundation.functions
open import foundation.equivalences
open import foundation.identity-types

open import univalent-combinatorics.standard-finite-types
open import univalent-combinatorics.involution-standard-finite-types
open import univalent-combinatorics.permutations-standard-finite-types

open import lists.lists
open import lists.arrays

open import linear-algebra.vectors
```

</details>

## Idea

Given an array `t` of length `n` and a automorphism `σ` of `Fin n`, the permutation of `t` according to `σ` is the array where the index are permuted by `σ`.
Then, we can define what is a permutation of a list of length `n` via the equivalence between arrays and lists.

## Definitions

```agda
module _
  {l : Level} {A : UU l}
  where

  permute-array : (t : array A) → Permutation (length-array t) → array A
  permute-array (n , f) s = n , (f ∘ (map-equiv s))

  permute-list : (l : list A) → Permutation (length-list l) → list A
  permute-list l s =
    map-equiv
      ( equiv-list-array)
      ( permute-array (map-equiv equiv-array-list l) s)

  permute-vec : {n : ℕ} → (v : vec A n) → Permutation n → vec A n
  permute-vec {n} v s =
    map-equiv (compute-vec n) (map-inv-equiv (compute-vec n) v ∘ (map-equiv s))

  compute-permute-vec-id-equiv :
    {n : ℕ}
    (v : vec A n) →
    permute-vec v id-equiv ＝ v
  compute-permute-vec-id-equiv {n} v =
    ap (λ f → map-equiv f v) (right-inverse-law-equiv (compute-vec n))
```
