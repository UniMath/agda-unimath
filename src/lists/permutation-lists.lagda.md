# Permutations of lists

```agda
module lists.permutation-lists where
```

<details><summary>Imports</summary>

```agda
open import finite-group-theory.permutations-standard-finite-types

open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.functions
open import foundation.universe-levels
open import foundation.identity-types

open import linear-algebra.vectors

open import lists.arrays
open import lists.lists
open import lists.permutation-vectors

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

### The predicate that a function from `list` to `list` is permuting lists

```agda
  is-permutation-list : (list A → list A) → UU l
  is-permutation-list f =
    (l : list A) →
    Σ ( Permutation (length-list l))
      ( λ t → f l ＝ permute-list l t)
```

## Properties

### If a function `f` from `vec` to `vec` is a permutation of vectors then `list-vec ∘ f ∘ vec-list` is a permutation of lists

```agda
  is-permutation-list-is-permutation-vec :
    (f : (n : ℕ) → vec A n → vec A n ) →
    ((n : ℕ) → is-permutation-vec n (f n)) →
    is-permutation-list
      ( λ l → list-vec (length-list l) (f (length-list l) (vec-list l)))
  pr1 (is-permutation-list-is-permutation-vec f T l) =
    pr1 (T (length-list l) (vec-list l))
  pr2 (is-permutation-list-is-permutation-vec f T l) =
    ap (λ p → list-vec (length-list l) p) (pr2 (T (length-list l) (vec-list l)))
```

### If `x` is in `permute-list l t` then `x` is in `l`

```agda
  is-in-list-is-permute-list :
    (l : list A) (t : Permutation (length-list l)) (x : A) →
    x ∈-list (permute-list l t) → x ∈-list l
  is-in-list-is-permute-list (cons x₁ l) t x I = {!!}
```
