# Quicksort for lists

```agda
module lists.quicksort-lists where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.strong-induction-natural-numbers

open import foundation.coproduct-types
open import foundation.identity-types
open import foundation.unit-type
open import foundation.universe-levels

open import lists.concatenation-lists
open import lists.lists

open import order-theory.decidable-total-orders
```

</details>

## Idea

{{#concept "Quicksort" Disambiguation="on lists" WD="quicksort" WDID=Q486598 Agda=quicksort-list}}
is a [sorting algorithm](lists.sorting-algorithms-lists.md) on
[lists](lists.lists.md) that works by selecting a pivoting element, dividing the
list into elements smaller than the pivoting element and elements greater than
the pivoting element, and sorting those two lists recursively by again applying
the quicksort algorithm. If the list is empty, the algorithm is done.

## Definition

```agda
module _
  {l1 l2 : Level} (X : Decidable-Total-Order l1 l2)
  where

  helper-quicksort-list-divide-leq :
    (x : type-Decidable-Total-Order X) →
    (y : type-Decidable-Total-Order X) →
    leq-or-strict-greater-Decidable-Poset X x y →
    list (type-Decidable-Total-Order X) →
    list (type-Decidable-Total-Order X)
  helper-quicksort-list-divide-leq x y (inl p) l = l
  helper-quicksort-list-divide-leq x y (inr p) l = cons y l

  quicksort-list-divide-leq :
    type-Decidable-Total-Order X → list (type-Decidable-Total-Order X) →
    list (type-Decidable-Total-Order X)
  quicksort-list-divide-leq x nil = nil
  quicksort-list-divide-leq x (cons y l) =
    helper-quicksort-list-divide-leq
      ( x)
      ( y)
      ( is-leq-or-strict-greater-Decidable-Total-Order X x y)
      ( quicksort-list-divide-leq x l)

  helper-quicksort-list-divide-strict-greater :
    (x : type-Decidable-Total-Order X) →
    (y : type-Decidable-Total-Order X) →
    leq-or-strict-greater-Decidable-Poset X x y →
    list (type-Decidable-Total-Order X) →
    list (type-Decidable-Total-Order X)
  helper-quicksort-list-divide-strict-greater x y (inl p) l = cons y l
  helper-quicksort-list-divide-strict-greater x y (inr p) l = l

  quicksort-list-divide-strict-greater :
    type-Decidable-Total-Order X → list (type-Decidable-Total-Order X) →
    list (type-Decidable-Total-Order X)
  quicksort-list-divide-strict-greater x nil = nil
  quicksort-list-divide-strict-greater x (cons y l) =
    helper-quicksort-list-divide-strict-greater
      ( x)
      ( y)
      ( is-leq-or-strict-greater-Decidable-Total-Order X x y)
      ( quicksort-list-divide-strict-greater x l)

  private
    helper-inequality-length-quicksort-list-divide-leq :
      (x : type-Decidable-Total-Order X) →
      (y : type-Decidable-Total-Order X) →
      (p : leq-or-strict-greater-Decidable-Poset X x y) →
      (l : list (type-Decidable-Total-Order X)) →
      length-list (helper-quicksort-list-divide-leq x y p l) ≤-ℕ
      length-list (cons y l)
    helper-inequality-length-quicksort-list-divide-leq x y (inl _) l =
      succ-leq-ℕ (length-list l)
    helper-inequality-length-quicksort-list-divide-leq x y (inr _) l =
      refl-leq-ℕ (length-list (cons y l))

    inequality-length-quicksort-list-divide-leq :
      (x : type-Decidable-Total-Order X) →
      (l : list (type-Decidable-Total-Order X)) →
      length-list (quicksort-list-divide-leq x l) ≤-ℕ length-list l
    inequality-length-quicksort-list-divide-leq x nil = star
    inequality-length-quicksort-list-divide-leq x (cons y l) =
      transitive-leq-ℕ
        ( length-list (quicksort-list-divide-leq x (cons y l)))
        ( length-list (cons y (quicksort-list-divide-leq x l)))
        ( length-list (cons y l))
        ( inequality-length-quicksort-list-divide-leq x l)
        ( helper-inequality-length-quicksort-list-divide-leq
            ( x)
            ( y)
            ( is-leq-or-strict-greater-Decidable-Total-Order X x y)
            ( quicksort-list-divide-leq x l))

    helper-inequality-length-quicksort-list-divide-strict-greater :
      (x : type-Decidable-Total-Order X) →
      (y : type-Decidable-Total-Order X) →
      (p : leq-or-strict-greater-Decidable-Poset X x y) →
      (l : list (type-Decidable-Total-Order X)) →
      length-list (helper-quicksort-list-divide-strict-greater x y p l) ≤-ℕ
      length-list (cons y l)
    helper-inequality-length-quicksort-list-divide-strict-greater
      ( x)
      ( y)
      ( inl _)
      ( l) =
      refl-leq-ℕ (length-list (cons y l))
    helper-inequality-length-quicksort-list-divide-strict-greater
      ( x)
      ( y)
      ( inr _)
      ( l) =
      succ-leq-ℕ (length-list l)

    inequality-length-quicksort-list-divide-strict-greater :
      (x : type-Decidable-Total-Order X) →
      (l : list (type-Decidable-Total-Order X)) →
      length-list (quicksort-list-divide-strict-greater x l) ≤-ℕ length-list l
    inequality-length-quicksort-list-divide-strict-greater x nil = star
    inequality-length-quicksort-list-divide-strict-greater x (cons y l) =
      transitive-leq-ℕ
        ( length-list (quicksort-list-divide-strict-greater x (cons y l)))
        ( length-list (cons y (quicksort-list-divide-strict-greater x l)))
        ( length-list (cons y l))
        ( inequality-length-quicksort-list-divide-strict-greater x l)
        ( helper-inequality-length-quicksort-list-divide-strict-greater
            ( x)
            ( y)
            ( is-leq-or-strict-greater-Decidable-Total-Order X x y)
            ( quicksort-list-divide-strict-greater x l))

  base-quicksort-list :
    (l : list (type-Decidable-Total-Order X)) → zero-ℕ ＝ length-list l →
    list (type-Decidable-Total-Order X)
  base-quicksort-list nil x = nil

  inductive-step-quicksort-list :
    (k : ℕ) →
    □-≤-ℕ
      ( λ n →
        (l : list (type-Decidable-Total-Order X)) →
        n ＝ length-list l → list (type-Decidable-Total-Order X))
      ( k) →
    (l : list (type-Decidable-Total-Order X)) →
    succ-ℕ k ＝ length-list l → list (type-Decidable-Total-Order X)
  inductive-step-quicksort-list k sort (cons x l) p =
    concat-list
      ( sort
          ( length-list (quicksort-list-divide-leq x l))
          ( transitive-leq-ℕ
              ( length-list (quicksort-list-divide-leq x l))
              ( length-list l)
              ( k)
              ( leq-eq-ℕ (length-list l) k (is-injective-succ-ℕ (inv p)))
              ( inequality-length-quicksort-list-divide-leq x l))
          ( quicksort-list-divide-leq x l)
          ( refl))
      ( cons
          ( x)
          ( sort
              ( length-list (quicksort-list-divide-strict-greater x l))
              ( transitive-leq-ℕ
                  ( length-list (quicksort-list-divide-strict-greater x l))
                  ( length-list l)
                  ( k)
                  ( leq-eq-ℕ (length-list l) k (is-injective-succ-ℕ (inv p)))
                  ( inequality-length-quicksort-list-divide-strict-greater x l))
              ( quicksort-list-divide-strict-greater x l)
              ( refl)))

  quicksort-list :
    list (type-Decidable-Total-Order X) →
    list (type-Decidable-Total-Order X)
  quicksort-list l =
    strong-ind-ℕ
      ( λ n →
        (l : list (type-Decidable-Total-Order X)) → n ＝ length-list l →
        list (type-Decidable-Total-Order X))
      ( base-quicksort-list)
      ( inductive-step-quicksort-list)
      ( length-list l)
      ( l)
      ( refl)
```
