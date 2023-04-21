# Permutations of lists and arrays

```agda
module lists.permutation-lists where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.functions
open import foundation.identity-types
open import foundation.unit-type
open import foundation.universe-levels

open import linear-algebra.vectors

open import lists.arrays
open import lists.lists

open import univalent-combinatorics.involution-standard-finite-types
open import univalent-combinatorics.permutations-standard-finite-types
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

Given an array `t` of length `n` and a automorphism `σ` of `Fin n`, the
permutation of `t` according to `σ` is the array where the index are permuted by
`σ`. Then, we can define what is a permutation of a list of length `n` via the
equivalence between arrays and lists.

## Definitions

### Permutation of an array , of a list and of vector

```agda
module _
  {l : Level} {A : UU l}
  where

  permute-array : (t : array A) → Permutation (length-array t) → array A
  permute-array (n , f) s = n , (f ∘ (map-equiv s))
-- TODO : Ask Egbert if I should replace (map-equiv s) by (map-inv-equiv s)

  permute-list : (l : list A) → Permutation (length-list l) → list A
  permute-list l s =
    map-equiv
      ( equiv-list-array)
      ( permute-array (map-equiv equiv-array-list l) s)

  permute-vec : (n : ℕ) → vec A n → Permutation n → vec A n
  permute-vec n v s =
    listed-vec-functional-vec n (functional-vec-vec n v ∘ (map-equiv s))
-- TODO : Ask Egbert if I should replace (map-equiv s) by (map-inv-equiv s)
```

### The predicate that a function from `vec` to `vec` is just permuting vectors.

```agda
  is-permutation-vec : (n : ℕ) → (vec A n → vec A n) → UU l
  is-permutation-vec n f =
    Σ ( (v : vec A n) → Permutation n)
      ( λ a → (v : vec A n) → f v ＝ permute-vec n v (a v))
```

## Properties

### Computational rules for `permute-vec`

```agda
  compute-permute-vec-id-equiv :
    (n : ℕ)
    (v : vec A n) →
    permute-vec n v id-equiv ＝ v
  compute-permute-vec-id-equiv n v =
    ap (λ f → map-equiv f v) (right-inverse-law-equiv (compute-vec n))

  compute-composition-permute-vec :
    (n : ℕ)
    (v : vec A n) →
    (a b : Permutation n) →
    permute-vec n v (a ∘e b) ＝ permute-vec n (permute-vec n v a) b
  compute-composition-permute-vec n v a b =
    ap
      ( λ f → listed-vec-functional-vec n (f ∘ (map-equiv b)))
      ( inv (isretr-functional-vec-vec n (functional-vec-vec n v ∘ map-equiv a)))

  compute-swap-two-last-elements-permutation-permute-vec :
    (n : ℕ)
    (v : vec A n) →
    (x y : A) →
    permute-vec
      (succ-ℕ (succ-ℕ n))
      (x ∷ y ∷ v)
      (swap-two-last-elements-permutation n) ＝
    (y ∷ x ∷ v)
  compute-swap-two-last-elements-permutation-permute-vec n v x y =
    eq-Eq-vec
      ( succ-ℕ (succ-ℕ n))
      ( permute-vec
          ( succ-ℕ (succ-ℕ n))
          ( x ∷ y ∷ v)
          ( swap-two-last-elements-permutation n))
      ( y ∷ x ∷ v)
      ( refl ,
        refl ,
        Eq-eq-vec
          ( n)
          ( permute-vec n v id-equiv)
          ( v)
          ( compute-permute-vec-id-equiv n v))

  ap-permute-vec :
    {n : ℕ}
    (a : Permutation n)
    {v w : vec A n} →
    v ＝ w →
    permute-vec n v a ＝ permute-vec n w a
  ap-permute-vec a refl = refl
```
