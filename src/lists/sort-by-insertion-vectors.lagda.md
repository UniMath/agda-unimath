# Sort by insertion for vectors

```agda
module lists.sort-by-insertion-vectors where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.universe-levels
open import foundation.unit-type
open import foundation.coproduct-types
open import foundation.functoriality-coproduct-types
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.functions
open import foundation.equivalences

open import univalent-combinatorics.standard-finite-types
open import univalent-combinatorics.permutations-standard-finite-types

open import lists.sorted-vectors
open import lists.permutation-lists
open import lists.sorting-algorithms-vectors

open import linear-algebra.vectors

open import order-theory.total-decidable-posets
```

</details>

## Idea

In these file, we define the sort by insertion on vectors and we prove its correcteness.

## Definition

```agda
module _
  {l1 l2 : Level} (X : total-decidable-Poset l1 l2)
  where

  insertion-sort-vec-helper :
    {n : ℕ}
    (x y : element-total-decidable-Poset X)
    (l : vec (element-total-decidable-Poset X) n) →
    leq-or-strict-greater-decidable-Poset X x y →
    vec (element-total-decidable-Poset X) (succ-ℕ (succ-ℕ (n )))
  insertion-sort-vec-helper x y l (inl p) = x ∷ y ∷ l
  insertion-sort-vec-helper {0} x y empty-vec (inr p) = y ∷ x ∷ empty-vec
  insertion-sort-vec-helper {succ-ℕ n} x y (z ∷ l) (inr p) =
    y ∷
    ( insertion-sort-vec-helper
        ( x)
        ( z)
        ( l)
        ( is-leq-or-strict-greater-total-decidable-Poset X x z))

  insertion-sort-vec :
    {n : ℕ} →
    vec (element-total-decidable-Poset X) n →
    vec (element-total-decidable-Poset X) n
  insertion-sort-vec {zero-ℕ} empty-vec = empty-vec
  insertion-sort-vec {1} l = l
  insertion-sort-vec {succ-ℕ (succ-ℕ n)} (x ∷ y ∷ l) =
    insertion-sort-vec-helper
      ( x)
      ( head-vec (insertion-sort-vec (y ∷ l)))
      ( tail-vec (insertion-sort-vec (y ∷ l)))
      ( is-leq-or-strict-greater-total-decidable-Poset X _ _)
```

## Properties

### Sort by insertion is a permutation

```agda
  permutation-insertion-sort-vec-helper :
    {n : ℕ}
    (x y : element-total-decidable-Poset X)
    (l : vec (element-total-decidable-Poset X) n) →
    leq-or-strict-greater-decidable-Poset X x y →
    Permutation (succ-ℕ (succ-ℕ (n)))
  permutation-insertion-sort-vec-helper x y l (inl _) = id-equiv
  permutation-insertion-sort-vec-helper {0} x y empty-vec (inr _) =
    two-cycle-permutation 2 (zero-Fin 1) (one-Fin 1)
  permutation-insertion-sort-vec-helper {succ-ℕ n} x y (z ∷ l) (inr _) =
    ( ( swap-two-last-elements-permutation (succ-ℕ n)) ∘e
      ( ( equiv-coprod
            ( permutation-insertion-sort-vec-helper
                ( x)
                ( z)
                ( l)
                ( is-leq-or-strict-greater-total-decidable-Poset X x z))
            ( id-equiv))))

  permutation-insertion-sort-vec :
    {n : ℕ}
    (v : vec (element-total-decidable-Poset X) n) →
    Permutation n
  permutation-insertion-sort-vec {zero-ℕ} empty-vec = id-equiv
  permutation-insertion-sort-vec {1} l = id-equiv
  permutation-insertion-sort-vec {succ-ℕ (succ-ℕ n)} (x ∷ y ∷ l) =
    equiv-coprod
      ( permutation-insertion-sort-vec (y ∷ l))
      ( id-equiv) ∘e
    permutation-insertion-sort-vec-helper
      ( x)
      ( head-vec (insertion-sort-vec (y ∷ l)))
      ( tail-vec (insertion-sort-vec (y ∷ l)))
      ( is-leq-or-strict-greater-total-decidable-Poset X _ _)

  is-permutation-insertion-sort-vec-helper :
    {n : ℕ}
    (x y : element-total-decidable-Poset X)
    (v : vec (element-total-decidable-Poset X) n)
    (p : leq-or-strict-greater-decidable-Poset X x y) →
    insertion-sort-vec-helper x y v p ＝
    permute-vec
      ( succ-ℕ (succ-ℕ n))
      ( x ∷ y ∷ v)
      ( permutation-insertion-sort-vec-helper x y v p)
  is-permutation-insertion-sort-vec-helper x y v (inl _) =
    inv (compute-permute-vec-id-equiv (succ-ℕ (succ-ℕ _)) (x ∷ y ∷ v))
  is-permutation-insertion-sort-vec-helper {zero-ℕ} x y empty-vec (inr _) =
    refl
  is-permutation-insertion-sort-vec-helper {succ-ℕ n} x y (z ∷ v) (inr p) =
    eq-Eq-vec
      ( succ-ℕ (succ-ℕ (succ-ℕ n)))
      ( insertion-sort-vec-helper x y (z ∷ v) (inr p))
      ( permute-vec
          ( succ-ℕ (succ-ℕ (succ-ℕ n)))
          ( x ∷ y ∷ z ∷ v)
          ( permutation-insertion-sort-vec-helper x y (z ∷ v) (inr p)))
      ( refl ,
        Eq-eq-vec
          ( succ-ℕ (succ-ℕ n))
          ( insertion-sort-vec-helper
              ( x)
              ( z)
              ( v)
              ( is-leq-or-strict-greater-total-decidable-Poset X x z))
          ( tail-vec
              ( permute-vec
                  ( succ-ℕ (succ-ℕ (succ-ℕ n)))
                  ( x ∷ y ∷ z ∷ v)
                  ( permutation-insertion-sort-vec-helper x y (z ∷ v) (inr p))))
          ( ( is-permutation-insertion-sort-vec-helper
                ( x)
                ( z)
                ( v)
                ( is-leq-or-strict-greater-total-decidable-Poset X x z)) ∙
            ap
              ( tail-vec)
              ( ap-permute-vec
                  ( equiv-coprod
                      ( permutation-insertion-sort-vec-helper
                          ( x)
                          ( z)
                          ( v)
                          ( is-leq-or-strict-greater-total-decidable-Poset
                              ( X)
                              ( x)
                              ( z)))
                      ( id-equiv))
                  ( inv
                     ( compute-swap-two-last-elements-permutation-permute-vec
                         (succ-ℕ n)
                         ( z ∷ v)
                         ( x)
                         ( y))) ∙
                inv
                  ( compute-composition-permute-vec
                      (succ-ℕ (succ-ℕ (succ-ℕ n)))
                      ( x ∷ y ∷ z ∷ v)
                      ( swap-two-last-elements-permutation (succ-ℕ n))
                      ( equiv-coprod
                          ( permutation-insertion-sort-vec-helper
                              ( x)
                              ( z)
                              ( v)
                              ( is-leq-or-strict-greater-total-decidable-Poset
                                  ( X)
                                  ( x)
                                  ( z)))
                          ( id-equiv))))))

  is-permutation-insertion-sort-vec :
    {n : ℕ}
    (v : vec (element-total-decidable-Poset X) n) →
    insertion-sort-vec v  ＝ permute-vec n v (permutation-insertion-sort-vec v)
  is-permutation-insertion-sort-vec {0} empty-vec = refl
  is-permutation-insertion-sort-vec {1} (x ∷ empty-vec) = refl
  is-permutation-insertion-sort-vec {succ-ℕ (succ-ℕ n)} (x ∷ y ∷ v) =
    is-permutation-insertion-sort-vec-helper
      ( x)
      ( head-vec (insertion-sort-vec (y ∷ v)))
      ( tail-vec (insertion-sort-vec (y  ∷ v)))
      ( is-leq-or-strict-greater-total-decidable-Poset X _ _) ∙
    ( ap-permute-vec
        ( permutation-insertion-sort-vec-helper
              ( x)
              ( head-vec (insertion-sort-vec (y ∷ v)))
              ( tail-vec (insertion-sort-vec (y ∷ v)))
              ( is-leq-or-strict-greater-total-decidable-Poset X _ _))
        (  ap
             ( λ l → x ∷ l)
             ( cons-head-tail-vec n (insertion-sort-vec (y ∷ v)) ∙
               is-permutation-insertion-sort-vec (y ∷ v))) ∙
      inv
        ( compute-composition-permute-vec
            (succ-ℕ (succ-ℕ n))
            ( x ∷ y ∷ v)
            ( equiv-coprod
                ( permutation-insertion-sort-vec (y ∷ v))
                ( id-equiv))
            ( permutation-insertion-sort-vec-helper
                ( x)
                ( head-vec (insertion-sort-vec (y ∷ v)))
                ( tail-vec (insertion-sort-vec (y ∷ v)))
                ( is-leq-or-strict-greater-total-decidable-Poset X _ _))))
```

### Sort by insertion is sorting vectors


```agda
  is-sorting-insertion-sort-vec-helper :
    {n : ℕ}
    (x y : element-total-decidable-Poset X)
    (v : vec (element-total-decidable-Poset X) n) →
    (p : leq-or-strict-greater-decidable-Poset X x y) →
    is-sorted-vec X (y ∷ v) →
    is-sorted-vec X (insertion-sort-vec-helper x y v p)
  is-sorting-insertion-sort-vec-helper {0} x y empty-vec (inl p) _ =
    p , raise-star
  is-sorting-insertion-sort-vec-helper {0} x y empty-vec (inr p) _ =
    pr2 p , raise-star
  is-sorting-insertion-sort-vec-helper {succ-ℕ n} x y l (inl p) s =
    p , s
  is-sorting-insertion-sort-vec-helper {succ-ℕ n} x y (z ∷ v) (inr p) s =
    is-sorted-vec-is-sorted-leq-all-element-vec-is-sorted-vec
      ( X)
      ( insertion-sort-vec-helper x y (z ∷ v) (inr p))
      ( tr
          ( λ l → is-leq-all-element-vec X y l)
          ( inv
              ( is-permutation-insertion-sort-vec-helper
                  ( x)
                  ( z)
                  ( v)
                  ( is-leq-or-strict-greater-total-decidable-Poset X x z)))
          ( is-leq-all-element-vec-permute-vec
              ( X)
              ( y)
              ( x ∷ z ∷ v)
              ( permutation-insertion-sort-vec-helper
                  ( x)
                  ( z)
                  ( v)
                  ( is-leq-or-strict-greater-total-decidable-Poset X x z))
              ( pr2 p ,
               pr1
                 ( is-sorted-leq-all-element-vec-is-sorted-vec
                     ( X)
                     ( y ∷ z ∷ v)
                     ( s)))) ,
         is-sorted-leq-all-element-vec-is-sorted-vec
           ( X)
           ( insertion-sort-vec-helper
               ( x)
               ( z)
               ( v)
               ( is-leq-or-strict-greater-total-decidable-Poset X x z))
           ( is-sorting-insertion-sort-vec-helper
               ( x)
               ( z)
               ( v)
               ( is-leq-or-strict-greater-total-decidable-Poset X x z)
               ( is-sorted-tail-is-sorted-vec X (y ∷ z ∷ v) s)))

  is-sorting-insertion-sort-vec :
    {n : ℕ}
    (v : vec (element-total-decidable-Poset X) n) →
    is-sorted-vec X (insertion-sort-vec v)
  is-sorting-insertion-sort-vec {0} v = raise-star
  is-sorting-insertion-sort-vec {1} v = raise-star
  is-sorting-insertion-sort-vec {succ-ℕ (succ-ℕ n)} (x ∷ y ∷ v) =
    is-sorting-insertion-sort-vec-helper
      ( x)
      ( head-vec (insertion-sort-vec (y ∷ v)))
      ( tail-vec (insertion-sort-vec (y ∷ v)))
      ( is-leq-or-strict-greater-total-decidable-Poset X _ _)
      ( tr
          ( λ l → is-sorted-vec X l)
          ( inv (cons-head-tail-vec n (insertion-sort-vec (y ∷ v))))
          ( is-sorting-insertion-sort-vec (y ∷ v)))
```

### Sort by insertion is a sort

```agda
  is-a-sort-insertion-sort-vec :
    is-a-sort-vec X (insertion-sort-vec)
  pr1 (pr1 (is-a-sort-insertion-sort-vec n)) = permutation-insertion-sort-vec
  pr2 (pr1 (is-a-sort-insertion-sort-vec n)) = is-permutation-insertion-sort-vec
  pr2 (is-a-sort-insertion-sort-vec n) = is-sorting-insertion-sort-vec
```
