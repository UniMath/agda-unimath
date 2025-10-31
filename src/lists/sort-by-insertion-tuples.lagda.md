# Sort by insertion for tuples

```agda
module lists.sort-by-insertion-tuples where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import finite-group-theory.permutations-standard-finite-types
open import finite-group-theory.transpositions-standard-finite-types

open import foundation.action-on-identifications-functions
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.functoriality-coproduct-types
open import foundation.identity-types
open import foundation.transport-along-identifications
open import foundation.unit-type
open import foundation.universe-levels

open import lists.permutation-tuples
open import lists.sorted-tuples
open import lists.sorting-algorithms-tuples
open import lists.tuples

open import order-theory.decidable-total-orders
```

</details>

## Idea

{{#concept "Sort by insertion" Disambiguation="for tuples" WD="insertion sort" WDID=Q117241 Agda=insertion-sort-tuple}}
is a recursive [sorting algorithm](lists.sorting-algorithms-lists.md) on
[tuples](lists.tuples.md). If a tuple is empty or with only one element then it
is sorted. Otherwise, we recursively sort the tail of the tuple. Then we compare
the head of the tuple to the head of the [sorted](lists.sorted-tuples.md) tail.
If the head is less or equal than the head of the tail the tuple is sorted.
Otherwise we permute the two elements and we recursively sort the tail of the
tuple.

## Definition

```agda
module _
  {l1 l2 : Level} (X : Decidable-Total-Order l1 l2)
  where

  helper-insertion-sort-tuple :
    {n : ℕ}
    (x y : type-Decidable-Total-Order X)
    (l : tuple (type-Decidable-Total-Order X) n) →
    leq-or-strict-greater-Decidable-Poset X x y →
    tuple (type-Decidable-Total-Order X) (succ-ℕ (succ-ℕ (n)))
  helper-insertion-sort-tuple x y l (inl p) = x ∷ y ∷ l
  helper-insertion-sort-tuple {0} x y empty-tuple (inr p) = y ∷ x ∷ empty-tuple
  helper-insertion-sort-tuple {succ-ℕ n} x y (z ∷ l) (inr p) =
    y ∷
    ( helper-insertion-sort-tuple
      ( x)
      ( z)
      ( l)
      ( is-leq-or-strict-greater-Decidable-Total-Order X x z))

  insertion-sort-tuple :
    {n : ℕ} →
    tuple (type-Decidable-Total-Order X) n →
    tuple (type-Decidable-Total-Order X) n
  insertion-sort-tuple {zero-ℕ} empty-tuple = empty-tuple
  insertion-sort-tuple {1} l = l
  insertion-sort-tuple {succ-ℕ (succ-ℕ n)} (x ∷ y ∷ l) =
    helper-insertion-sort-tuple
      ( x)
      ( head-tuple (insertion-sort-tuple (y ∷ l)))
      ( tail-tuple (insertion-sort-tuple (y ∷ l)))
      ( is-leq-or-strict-greater-Decidable-Total-Order X _ _)
```

## Properties

### Sort by insertion is a permutation

```agda
  helper-permutation-insertion-sort-tuple :
    {n : ℕ}
    (x y : type-Decidable-Total-Order X)
    (l : tuple (type-Decidable-Total-Order X) n) →
    leq-or-strict-greater-Decidable-Poset X x y →
    Permutation (succ-ℕ (succ-ℕ (n)))
  helper-permutation-insertion-sort-tuple x y l (inl _) = id-equiv
  helper-permutation-insertion-sort-tuple {0} x y empty-tuple (inr _) =
    swap-two-last-elements-transposition-Fin 0
  helper-permutation-insertion-sort-tuple {succ-ℕ n} x y (z ∷ l) (inr _) =
    ( ( swap-two-last-elements-transposition-Fin (succ-ℕ n)) ∘e
      ( ( equiv-coproduct
          ( helper-permutation-insertion-sort-tuple
            ( x)
            ( z)
            ( l)
            ( is-leq-or-strict-greater-Decidable-Total-Order X x z))
          ( id-equiv))))

  permutation-insertion-sort-tuple :
    {n : ℕ}
    (v : tuple (type-Decidable-Total-Order X) n) →
    Permutation n
  permutation-insertion-sort-tuple {zero-ℕ} empty-tuple = id-equiv
  permutation-insertion-sort-tuple {1} l = id-equiv
  permutation-insertion-sort-tuple {succ-ℕ (succ-ℕ n)} (x ∷ y ∷ l) =
    equiv-coproduct
      ( permutation-insertion-sort-tuple (y ∷ l))
      ( id-equiv) ∘e
    helper-permutation-insertion-sort-tuple
      ( x)
      ( head-tuple (insertion-sort-tuple (y ∷ l)))
      ( tail-tuple (insertion-sort-tuple (y ∷ l)))
      ( is-leq-or-strict-greater-Decidable-Total-Order X _ _)

  helper-eq-permute-tuple-permutation-insertion-sort-tuple :
    {n : ℕ}
    (x y : type-Decidable-Total-Order X)
    (v : tuple (type-Decidable-Total-Order X) n)
    (p : leq-or-strict-greater-Decidable-Poset X x y) →
    helper-insertion-sort-tuple x y v p ＝
    permute-tuple
      ( succ-ℕ (succ-ℕ n))
      ( x ∷ y ∷ v)
      ( helper-permutation-insertion-sort-tuple x y v p)
  helper-eq-permute-tuple-permutation-insertion-sort-tuple x y v (inl _) =
    inv (compute-permute-tuple-id-equiv (succ-ℕ (succ-ℕ _)) (x ∷ y ∷ v))
  helper-eq-permute-tuple-permutation-insertion-sort-tuple
    {0}
    ( x)
    ( y)
    ( empty-tuple)
    ( inr _) =
    refl
  helper-eq-permute-tuple-permutation-insertion-sort-tuple
    {succ-ℕ n}
    ( x)
    ( y)
    ( z ∷ v)
    ( inr p) =
    eq-Eq-tuple
      ( succ-ℕ (succ-ℕ (succ-ℕ n)))
      ( helper-insertion-sort-tuple x y (z ∷ v) (inr p))
      ( permute-tuple
        ( succ-ℕ (succ-ℕ (succ-ℕ n)))
        ( x ∷ y ∷ z ∷ v)
        ( helper-permutation-insertion-sort-tuple x y (z ∷ v) (inr p)))
      ( refl ,
        Eq-eq-tuple
          ( succ-ℕ (succ-ℕ n))
          ( helper-insertion-sort-tuple
            ( x)
            ( z)
            ( v)
            ( is-leq-or-strict-greater-Decidable-Total-Order X x z))
          ( tail-tuple
            ( permute-tuple
              ( succ-ℕ (succ-ℕ (succ-ℕ n)))
              ( x ∷ y ∷ z ∷ v)
              ( helper-permutation-insertion-sort-tuple x y (z ∷ v) (inr p))))
          ( ( helper-eq-permute-tuple-permutation-insertion-sort-tuple
              ( x)
              ( z)
              ( v)
              ( is-leq-or-strict-greater-Decidable-Total-Order X x z)) ∙
            ( ap
              ( tail-tuple)
              ( ap-permute-tuple
                ( equiv-coproduct
                  ( helper-permutation-insertion-sort-tuple
                    ( x)
                    ( z)
                    ( v)
                    ( is-leq-or-strict-greater-Decidable-Total-Order
                      ( X)
                      ( x)
                      ( z)))
                  ( id-equiv))
                ( inv
                  ( compute-swap-two-last-elements-transposition-Fin-permute-tuple
                    (succ-ℕ n)
                    ( z ∷ v)
                    ( x)
                    ( y))) ∙
                ( inv
                  ( compute-composition-permute-tuple
                    (succ-ℕ (succ-ℕ (succ-ℕ n)))
                    ( x ∷ y ∷ z ∷ v)
                    ( swap-two-last-elements-transposition-Fin (succ-ℕ n))
                    ( equiv-coproduct
                      ( helper-permutation-insertion-sort-tuple
                        ( x)
                        ( z)
                        ( v)
                        ( is-leq-or-strict-greater-Decidable-Total-Order
                          ( X)
                          ( x)
                          ( z)))
                        ( id-equiv))))))))

  eq-permute-tuple-permutation-insertion-sort-tuple :
    {n : ℕ}
    (v : tuple (type-Decidable-Total-Order X) n) →
    insertion-sort-tuple v ＝
    permute-tuple n v (permutation-insertion-sort-tuple v)
  eq-permute-tuple-permutation-insertion-sort-tuple {0} empty-tuple = refl
  eq-permute-tuple-permutation-insertion-sort-tuple {1} (x ∷ empty-tuple) = refl
  eq-permute-tuple-permutation-insertion-sort-tuple
    {succ-ℕ (succ-ℕ n)}
    ( x ∷ y ∷ v) =
    ( ( helper-eq-permute-tuple-permutation-insertion-sort-tuple
        ( x)
        ( head-tuple (insertion-sort-tuple (y ∷ v)))
        ( tail-tuple (insertion-sort-tuple (y ∷ v)))
        ( is-leq-or-strict-greater-Decidable-Total-Order X _ _)) ∙
      ( ( ap-permute-tuple
          ( helper-permutation-insertion-sort-tuple
            ( x)
            ( head-tuple (insertion-sort-tuple (y ∷ v)))
            ( tail-tuple (insertion-sort-tuple (y ∷ v)))
            ( is-leq-or-strict-greater-Decidable-Total-Order X _ _))
          ( ap
            ( λ l → x ∷ l)
            ( cons-head-tail-tuple n (insertion-sort-tuple (y ∷ v)) ∙
              eq-permute-tuple-permutation-insertion-sort-tuple (y ∷ v)))) ∙
        ( ( inv
            ( compute-composition-permute-tuple
              (succ-ℕ (succ-ℕ n))
              ( x ∷ y ∷ v)
              ( equiv-coproduct
                ( permutation-insertion-sort-tuple (y ∷ v))
                ( id-equiv))
              ( helper-permutation-insertion-sort-tuple
                ( x)
                ( head-tuple (insertion-sort-tuple (y ∷ v)))
                ( tail-tuple (insertion-sort-tuple (y ∷ v)))
                ( is-leq-or-strict-greater-Decidable-Total-Order X _ _)))))))
```

### Sort by insertion is sorting tuples

```agda
  helper-is-sorting-insertion-sort-tuple :
    {n : ℕ}
    (x y : type-Decidable-Total-Order X)
    (v : tuple (type-Decidable-Total-Order X) n) →
    (p : leq-or-strict-greater-Decidable-Poset X x y) →
    is-sorted-tuple X (y ∷ v) →
    is-sorted-tuple X (helper-insertion-sort-tuple x y v p)
  helper-is-sorting-insertion-sort-tuple {0} x y empty-tuple (inl p) _ =
    p , raise-star
  helper-is-sorting-insertion-sort-tuple {0} x y empty-tuple (inr p) _ =
    pr2 p , raise-star
  helper-is-sorting-insertion-sort-tuple {succ-ℕ n} x y l (inl p) s =
    p , s
  helper-is-sorting-insertion-sort-tuple {succ-ℕ n} x y (z ∷ v) (inr p) s =
    is-sorted-tuple-is-sorted-least-element-tuple
      ( X)
      ( helper-insertion-sort-tuple x y (z ∷ v) (inr p))
      ( tr
        ( is-least-element-tuple X y)
        ( inv
          ( helper-eq-permute-tuple-permutation-insertion-sort-tuple
            ( x)
            ( z)
            ( v)
            ( is-leq-or-strict-greater-Decidable-Total-Order X x z)))
        ( is-least-element-permute-tuple
          ( X)
          ( y)
          ( x ∷ z ∷ v)
          ( helper-permutation-insertion-sort-tuple
            ( x)
            ( z)
            ( v)
            ( is-leq-or-strict-greater-Decidable-Total-Order X x z))
          ( pr2 p ,
            pr1
              ( is-sorted-least-element-tuple-is-sorted-tuple
                ( X)
                ( y ∷ z ∷ v)
                ( s)))) ,
        ( is-sorted-least-element-tuple-is-sorted-tuple
          ( X)
          ( helper-insertion-sort-tuple
            ( x)
            ( z)
            ( v)
            ( is-leq-or-strict-greater-Decidable-Total-Order X x z))
          ( helper-is-sorting-insertion-sort-tuple
            ( x)
            ( z)
            ( v)
            ( is-leq-or-strict-greater-Decidable-Total-Order X x z)
            ( is-sorted-tail-is-sorted-tuple X (y ∷ z ∷ v) s))))

  is-sorting-insertion-sort-tuple :
    {n : ℕ}
    (v : tuple (type-Decidable-Total-Order X) n) →
    is-sorted-tuple X (insertion-sort-tuple v)
  is-sorting-insertion-sort-tuple {0} v = raise-star
  is-sorting-insertion-sort-tuple {1} v = raise-star
  is-sorting-insertion-sort-tuple {succ-ℕ (succ-ℕ n)} (x ∷ y ∷ v) =
    helper-is-sorting-insertion-sort-tuple
      ( x)
      ( head-tuple (insertion-sort-tuple (y ∷ v)))
      ( tail-tuple (insertion-sort-tuple (y ∷ v)))
      ( is-leq-or-strict-greater-Decidable-Total-Order X _ _)
      ( tr
        ( λ l → is-sorted-tuple X l)
        ( inv (cons-head-tail-tuple n (insertion-sort-tuple (y ∷ v))))
        ( is-sorting-insertion-sort-tuple (y ∷ v)))
```

### Sort by insertion is a sort

```agda
  is-sort-insertion-sort-tuple :
    is-sort-tuple X (insertion-sort-tuple)
  pr1 (pr1 (is-sort-insertion-sort-tuple n) v) =
    permutation-insertion-sort-tuple v
  pr2 (pr1 (is-sort-insertion-sort-tuple n) v) =
    eq-permute-tuple-permutation-insertion-sort-tuple v
  pr2 (is-sort-insertion-sort-tuple n) = is-sorting-insertion-sort-tuple
```
