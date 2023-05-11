# Permutations of lists

```agda
module lists.permutation-lists where
```

<details><summary>Imports</summary>

```agda
open import finite-group-theory.permutations-standard-finite-types

open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.functions
open import foundation.universe-levels

open import linear-algebra.vectors

open import lists.arrays
open import lists.lists

open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

Given an array `t` of length `n` and a automorphism `σ` of `Fin n`, the
permutation of `t` according to `σ` is the array where the index are permuted by
`σ`. Then, we can define what is a permutation of a list of length `n` via the
equivalence between arrays and lists.

## Definition

```agda
module _
  {l : Level} {A : UU l}
  where

  permute-list : (l : list A) → Permutation (length-list l) → list A
  permute-list l s =
    list-array
      ( length-array (array-list l) ,
        functional-vec-array (array-list l) ∘ (map-equiv s))
```
