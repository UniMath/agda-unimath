# Quick sort for vectors

```agda
module lists.quick-sort-vectors where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.strong-induction-natural-numbers

open import foundation.universe-levels
open import foundation.propositions
open import foundation.unit-type
open import foundation.empty-types
open import foundation.cartesian-product-types
open import foundation.coproduct-types
open import foundation.functoriality-coproduct-types
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.functions
open import foundation.equivalences

open import univalent-combinatorics.standard-finite-types
open import univalent-combinatorics.permutations-standard-finite-types

open import lists.lists
open import lists.arrays
open import lists.concatenation-lists
open import lists.permutation-lists

open import linear-algebra.vectors

open import order-theory.total-decidable-posets
```

</details>

## Idea

In these file, we define the quick sort.

## Definition

```agda
module _
  {l1 l2 : Level} (X : total-decidable-Poset l1 l2)
  where

  quick-sort-list-divide-leq-helper :
    (x : element-total-decidable-Poset X) →
    (y : element-total-decidable-Poset X) →
    leq-or-strict-greater-decidable-Poset X x y →
    list (element-total-decidable-Poset X) →
    list (element-total-decidable-Poset X)
  quick-sort-list-divide-leq-helper x y (inl p) l = l
  quick-sort-list-divide-leq-helper x y (inr p) l = cons y l

  quick-sort-list-divide-leq :
    element-total-decidable-Poset X → list (element-total-decidable-Poset X) →
    list (element-total-decidable-Poset X)
  quick-sort-list-divide-leq x nil = nil
  quick-sort-list-divide-leq x (cons y l) =
    quick-sort-list-divide-leq-helper
      ( x)
      ( y)
      ( is-leq-or-strict-greater-total-decidable-Poset X x y)
      ( quick-sort-list-divide-leq x l)

  quick-sort-list-divide-strict-greater-helper :
    (x : element-total-decidable-Poset X) →
    (y : element-total-decidable-Poset X) →
    leq-or-strict-greater-decidable-Poset X x y →
    list (element-total-decidable-Poset X) →
    list (element-total-decidable-Poset X)
  quick-sort-list-divide-strict-greater-helper x y (inl p) l = cons y l
  quick-sort-list-divide-strict-greater-helper x y (inr p) l = l

  quick-sort-list-divide-strict-greater :
    element-total-decidable-Poset X → list (element-total-decidable-Poset X) →
    list (element-total-decidable-Poset X)
  quick-sort-list-divide-strict-greater x nil = nil
  quick-sort-list-divide-strict-greater x (cons y l) =
    quick-sort-list-divide-strict-greater-helper
      ( x)
      ( y)
      ( is-leq-or-strict-greater-total-decidable-Poset X x y)
      ( quick-sort-list-divide-strict-greater x l)

  private
    inequality-length-quick-sort-list-divide-leq-helper :
      (x : element-total-decidable-Poset X) →
      (y : element-total-decidable-Poset X) →
      (p : leq-or-strict-greater-decidable-Poset X x y) →
      (l : list (element-total-decidable-Poset X)) →
      length-list (quick-sort-list-divide-leq-helper x y p l) ≤-ℕ length-list (cons y l)
    inequality-length-quick-sort-list-divide-leq-helper x y (inl _) l =
      succ-leq-ℕ (length-list l)
    inequality-length-quick-sort-list-divide-leq-helper x y (inr _) l =
      refl-leq-ℕ (length-list (cons y l))

    inequality-length-quick-sort-list-divide-leq :
      (x : element-total-decidable-Poset X) →
      (l : list (element-total-decidable-Poset X)) →
      length-list (quick-sort-list-divide-leq x l) ≤-ℕ length-list l
    inequality-length-quick-sort-list-divide-leq x nil = star
    inequality-length-quick-sort-list-divide-leq x (cons y l) =
      transitive-leq-ℕ
        ( length-list (quick-sort-list-divide-leq x (cons y l)))
        ( length-list (cons y (quick-sort-list-divide-leq x l)) )
        ( length-list (cons y l))
        ( inequality-length-quick-sort-list-divide-leq x l)
        ( inequality-length-quick-sort-list-divide-leq-helper
            ( x)
            ( y)
            ( is-leq-or-strict-greater-total-decidable-Poset X x y)
            ( quick-sort-list-divide-leq x l))

    inequality-length-quick-sort-list-divide-strict-greater-helper :
      (x : element-total-decidable-Poset X) →
      (y : element-total-decidable-Poset X) →
      (p : leq-or-strict-greater-decidable-Poset X x y) →
      (l : list (element-total-decidable-Poset X)) →
      length-list (quick-sort-list-divide-strict-greater-helper x y p l) ≤-ℕ length-list (cons y l)
    inequality-length-quick-sort-list-divide-strict-greater-helper x y (inl _) l =
      refl-leq-ℕ (length-list (cons y l))
    inequality-length-quick-sort-list-divide-strict-greater-helper x y (inr _) l =
      succ-leq-ℕ (length-list l)

    inequality-length-quick-sort-list-divide-strict-greater :
      (x : element-total-decidable-Poset X) →
      (l : list (element-total-decidable-Poset X)) →
      length-list (quick-sort-list-divide-strict-greater x l) ≤-ℕ length-list l
    inequality-length-quick-sort-list-divide-strict-greater x nil = star
    inequality-length-quick-sort-list-divide-strict-greater x (cons y l) =
      transitive-leq-ℕ
        ( length-list (quick-sort-list-divide-strict-greater x (cons y l)))
        ( length-list (cons y (quick-sort-list-divide-strict-greater x l)) )
        ( length-list (cons y l))
        ( inequality-length-quick-sort-list-divide-strict-greater x l)
        ( inequality-length-quick-sort-list-divide-strict-greater-helper
            ( x)
            ( y)
            ( is-leq-or-strict-greater-total-decidable-Poset X x y)
            ( quick-sort-list-divide-strict-greater x l))

  base-quick-sort-list :
    (l : list (element-total-decidable-Poset X)) → zero-ℕ ＝ length-list l →
    list (element-total-decidable-Poset X)
  base-quick-sort-list nil x = nil

  inductive-step-quick-sort-list :
    (k : ℕ) →
    □-≤-ℕ
    ( λ n →
         (l : list (element-total-decidable-Poset X)) →
         n ＝ length-list l → list (element-total-decidable-Poset X))
    k →
    (l : list (element-total-decidable-Poset X)) →
    succ-ℕ k ＝ length-list l → list (element-total-decidable-Poset X)
  inductive-step-quick-sort-list k sort (cons x l) p =
    concat-list
      ( sort
          ( length-list (quick-sort-list-divide-leq x l))
          ( transitive-leq-ℕ
              ( length-list (quick-sort-list-divide-leq x l))
              ( length-list l)
              ( k)
              ( leq-eq-ℕ (length-list l) k (eq-succ-ℕ (inv p)))
              ( inequality-length-quick-sort-list-divide-leq x l))
          ( quick-sort-list-divide-leq x l)
          ( refl))
      ( cons
          ( x)
          ( sort
              ( length-list (quick-sort-list-divide-strict-greater x l))
              ( transitive-leq-ℕ
                  ( length-list (quick-sort-list-divide-strict-greater x l))
                  ( length-list l)
                  ( k)
                  ( leq-eq-ℕ (length-list l) k (eq-succ-ℕ (inv p)))
                  ( inequality-length-quick-sort-list-divide-strict-greater x l))
              ( quick-sort-list-divide-strict-greater x l)
              ( refl)))

  quick-sort-list :
    list (element-total-decidable-Poset X) →
    list (element-total-decidable-Poset X)
  quick-sort-list l =
    strong-ind-ℕ
      ( λ n →
        (l : list (element-total-decidable-Poset X)) → n ＝ length-list l →
        list (element-total-decidable-Poset X))
      ( base-quick-sort-list)
      ( inductive-step-quick-sort-list)
      ( length-list l)
      ( l)
      ( refl)
```
