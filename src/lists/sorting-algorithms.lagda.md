# Sorting algorithms

```agda
module lists.sorting-algorithms where
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
open import lists.sorting-lists
open import lists.permutation-lists

open import linear-algebra.vectors

open import order-theory.total-decidable-posets
```

</details>

## Idea

In these file we define the notion of sorting algorithms. Then we give some examples and prove their correctness.

## Definitions

### Sorting algorithms

```agda
```

### Sort by insertion

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

### Quick sort

-- ```agda
-- --   quick-sort-list-divide-leq-helper :
-- --     (x : element-total-decidable-Poset X) →
-- --     (y : element-total-decidable-Poset X) →
-- --     leq-or-strict-greater-decidable-Poset X x y →
-- --     list (element-total-decidable-Poset X) →
-- --     list (element-total-decidable-Poset X)
-- --   quick-sort-list-divide-leq-helper x y (inl p) l = l
-- --   quick-sort-list-divide-leq-helper x y (inr p) l = cons y l

-- --   quick-sort-list-divide-leq :
-- --     element-total-decidable-Poset X → list (element-total-decidable-Poset X) →
-- --     list (element-total-decidable-Poset X)
-- --   quick-sort-list-divide-leq x nil = nil
-- --   quick-sort-list-divide-leq x (cons y l) =
-- --     quick-sort-list-divide-leq-helper
-- --       ( x)
-- --       ( y)
-- --       ( is-leq-or-strict-greater-total-decidable-Poset X x y)
-- --       ( quick-sort-list-divide-leq x l)

-- --   quick-sort-list-divide-strict-greater-helper :
-- --     (x : element-total-decidable-Poset X) →
-- --     (y : element-total-decidable-Poset X) →
-- --     leq-or-strict-greater-decidable-Poset X x y →
-- --     list (element-total-decidable-Poset X) →
-- --     list (element-total-decidable-Poset X)
-- --   quick-sort-list-divide-strict-greater-helper x y (inl p) l = cons y l
-- --   quick-sort-list-divide-strict-greater-helper x y (inr p) l = l

-- --   quick-sort-list-divide-strict-greater :
-- --     element-total-decidable-Poset X → list (element-total-decidable-Poset X) →
-- --     list (element-total-decidable-Poset X)
-- --   quick-sort-list-divide-strict-greater x nil = nil
-- --   quick-sort-list-divide-strict-greater x (cons y l) =
-- --     quick-sort-list-divide-strict-greater-helper
-- --       ( x)
-- --       ( y)
-- --       ( is-leq-or-strict-greater-total-decidable-Poset X x y)
-- --       ( quick-sort-list-divide-strict-greater x l)

-- --   private
-- --     inequality-length-quick-sort-list-divide-leq-helper :
-- --       (x : element-total-decidable-Poset X) →
-- --       (y : element-total-decidable-Poset X) →
-- --       (p : leq-or-strict-greater-decidable-Poset X x y) →
-- --       (l : list (element-total-decidable-Poset X)) →
-- --       length-list (quick-sort-list-divide-leq-helper x y p l) ≤-ℕ length-list (cons y l)
-- --     inequality-length-quick-sort-list-divide-leq-helper x y (inl _) l =
-- --       succ-leq-ℕ (length-list l)
-- --     inequality-length-quick-sort-list-divide-leq-helper x y (inr _) l =
-- --       refl-leq-ℕ (length-list (cons y l))

-- --     inequality-length-quick-sort-list-divide-leq :
-- --       (x : element-total-decidable-Poset X) →
-- --       (l : list (element-total-decidable-Poset X)) →
-- --       length-list (quick-sort-list-divide-leq x l) ≤-ℕ length-list l
-- --     inequality-length-quick-sort-list-divide-leq x nil = star
-- --     inequality-length-quick-sort-list-divide-leq x (cons y l) =
-- --       transitive-leq-ℕ
-- --         ( length-list (quick-sort-list-divide-leq x (cons y l)))
-- --         ( length-list (cons y (quick-sort-list-divide-leq x l)) )
-- --         ( length-list (cons y l))
-- --         ( inequality-length-quick-sort-list-divide-leq x l)
-- --         ( inequality-length-quick-sort-list-divide-leq-helper
-- --             ( x)
-- --             ( y)
-- --             ( is-leq-or-strict-greater-total-decidable-Poset X x y)
-- --             ( quick-sort-list-divide-leq x l))

-- --     inequality-length-quick-sort-list-divide-strict-greater-helper :
-- --       (x : element-total-decidable-Poset X) →
-- --       (y : element-total-decidable-Poset X) →
-- --       (p : leq-or-strict-greater-decidable-Poset X x y) →
-- --       (l : list (element-total-decidable-Poset X)) →
-- --       length-list (quick-sort-list-divide-strict-greater-helper x y p l) ≤-ℕ length-list (cons y l)
-- --     inequality-length-quick-sort-list-divide-strict-greater-helper x y (inl _) l =
-- --       refl-leq-ℕ (length-list (cons y l))
-- --     inequality-length-quick-sort-list-divide-strict-greater-helper x y (inr _) l =
-- --       succ-leq-ℕ (length-list l)

-- --     inequality-length-quick-sort-list-divide-strict-greater :
-- --       (x : element-total-decidable-Poset X) →
-- --       (l : list (element-total-decidable-Poset X)) →
-- --       length-list (quick-sort-list-divide-strict-greater x l) ≤-ℕ length-list l
-- --     inequality-length-quick-sort-list-divide-strict-greater x nil = star
-- --     inequality-length-quick-sort-list-divide-strict-greater x (cons y l) =
-- --       transitive-leq-ℕ
-- --         ( length-list (quick-sort-list-divide-strict-greater x (cons y l)))
-- --         ( length-list (cons y (quick-sort-list-divide-strict-greater x l)) )
-- --         ( length-list (cons y l))
-- --         ( inequality-length-quick-sort-list-divide-strict-greater x l)
-- --         ( inequality-length-quick-sort-list-divide-strict-greater-helper
-- --             ( x)
-- --             ( y)
-- --             ( is-leq-or-strict-greater-total-decidable-Poset X x y)
-- --             ( quick-sort-list-divide-strict-greater x l))

-- --   base-quick-sort-list :
-- --     (l : list (element-total-decidable-Poset X)) → zero-ℕ ＝ length-list l →
-- --     list (element-total-decidable-Poset X)
-- --   base-quick-sort-list nil x = nil

-- --   inductive-step-quick-sort-list :
-- --     (k : ℕ) →
-- --     □-≤-ℕ
-- --     ( λ n →
-- --          (l : list (element-total-decidable-Poset X)) →
-- --          n ＝ length-list l → list (element-total-decidable-Poset X))
-- --     k →
-- --     (l : list (element-total-decidable-Poset X)) →
-- --     succ-ℕ k ＝ length-list l → list (element-total-decidable-Poset X)
-- --   inductive-step-quick-sort-list k sort (cons x l) p =
-- --     concat-list
-- --       ( sort
-- --           ( length-list (quick-sort-list-divide-leq x l))
-- --           ( transitive-leq-ℕ
-- --               ( length-list (quick-sort-list-divide-leq x l))
-- --               ( length-list l)
-- --               ( k)
-- --               ( leq-eq-ℕ (length-list l) k (eq-succ-ℕ (inv p)))
-- --               ( inequality-length-quick-sort-list-divide-leq x l))
-- --           ( quick-sort-list-divide-leq x l)
-- --           ( refl))
-- --       ( cons
-- --           ( x)
-- --           ( sort
-- --               ( length-list (quick-sort-list-divide-strict-greater x l))
-- --               ( transitive-leq-ℕ
-- --                   ( length-list (quick-sort-list-divide-strict-greater x l))
-- --                   ( length-list l)
-- --                   ( k)
-- --                   ( leq-eq-ℕ (length-list l) k (eq-succ-ℕ (inv p)))
-- --                   ( inequality-length-quick-sort-list-divide-strict-greater x l))
-- --               ( quick-sort-list-divide-strict-greater x l)
-- --               ( refl)))

-- --   quick-sort-list :
-- --     list (element-total-decidable-Poset X) →
-- --     list (element-total-decidable-Poset X)
-- --   quick-sort-list l =
-- --     strong-ind-ℕ
-- --       ( λ n →
-- --         (l : list (element-total-decidable-Poset X)) → n ＝ length-list l →
-- --         list (element-total-decidable-Poset X))
-- --       ( base-quick-sort-list)
-- --       ( inductive-step-quick-sort-list)
-- --       ( length-list l)
-- --       ( l)
-- --       ( refl)
```

## Properties

We show that the algorithms defined below are sorting algorithms.

### Sort by insertion

#### Is a permutation

```agda
  insertion-sort-vec-permutation-helper :
    {n : ℕ}
    (x y : element-total-decidable-Poset X)
    (l : vec (element-total-decidable-Poset X) n) →
    leq-or-strict-greater-decidable-Poset X x y →
    Permutation (succ-ℕ (succ-ℕ (n)))
  insertion-sort-vec-permutation-helper x y l (inl _) = id-equiv
  insertion-sort-vec-permutation-helper {0} x y empty-vec (inr _) =
    two-cycle-permutation 2 (zero-Fin 1) (one-Fin 1)
  insertion-sort-vec-permutation-helper {succ-ℕ n} x y (z ∷ l) (inr _) =
    ( ( swap-two-last-element-permutation (succ-ℕ n)) ∘e
      ( ( equiv-coprod
            ( insertion-sort-vec-permutation-helper
                ( x)
                ( z)
                ( l)
                ( is-leq-or-strict-greater-total-decidable-Poset X x z))
            ( id-equiv))))

  insertion-sort-vec-permutation :
    {n : ℕ}
    (v : vec (element-total-decidable-Poset X) n) →
    Permutation n
  insertion-sort-vec-permutation {zero-ℕ} empty-vec = id-equiv
  insertion-sort-vec-permutation {1} l = id-equiv
  insertion-sort-vec-permutation {succ-ℕ (succ-ℕ n)} (x ∷ y ∷ l) =
    insertion-sort-vec-permutation-helper
      ( x)
      ( head-vec (insertion-sort-vec (y ∷ l)))
      ( tail-vec (insertion-sort-vec (y ∷ l)))
      ( is-leq-or-strict-greater-total-decidable-Poset X _ _)

  is-permutation-insertion-sort-vec-helper :
    {n : ℕ}
    (x y : element-total-decidable-Poset X)
    (v : vec (element-total-decidable-Poset X) n)
    (p : leq-or-strict-greater-decidable-Poset X x y) →
    Eq-vec
      ( succ-ℕ (succ-ℕ n))
      ( insertion-sort-vec-helper x y v p)
      ( permute-vec (x ∷ y ∷ v) (insertion-sort-vec-permutation-helper x y v p ))
  is-permutation-insertion-sort-vec-helper x y v (inl _) =
    Eq-eq-vec
      ( succ-ℕ (succ-ℕ _))
      ( x ∷ y ∷ v)
      ( permute-vec (x ∷ y ∷ v) id-equiv)
      ( inv (compute-permute-vec-id-equiv (x ∷ y ∷ v)))
  is-permutation-insertion-sort-vec-helper {zero-ℕ} x y empty-vec (inr _) =
    refl , (refl , raise-star)
  is-permutation-insertion-sort-vec-helper {succ-ℕ n} x y (z ∷ v) (inr x1) =
    refl , {!!}

  is-permutation-insertion-sort-vec :
    {n : ℕ}
    (v : vec (element-total-decidable-Poset X) n) →
    Eq-vec
      ( n)
      ( insertion-sort-vec v)
      ( permute-vec v (insertion-sort-vec-permutation v))
  is-permutation-insertion-sort-vec v = {!!}
```

#### Is sorting vectors

```agda
  
  is-sorting-insertion-sort-vec-helper :
    (x y : element-total-decidable-Poset X)
    (n : ℕ)
    (l : vec (element-total-decidable-Poset X) n) →
    (p : leq-or-strict-greater-decidable-Poset X x y) →
    is-sorted-vec X (y ∷ l) →
    is-sorted-vec X (insertion-sort-vec-helper x y l p)
  is-sorting-insertion-sort-vec-helper x y zero-ℕ empty-vec (inl p) _ =
    p , raise-star
  is-sorting-insertion-sort-vec-helper x y zero-ℕ empty-vec (inr p) _ =
    pr2 p , raise-star
  is-sorting-insertion-sort-vec-helper x y 1 l (inl p) s =
    p , s
  is-sorting-insertion-sort-vec-helper x y 1 (z ∷ empty-vec) (inr p) s =
    is-sorted-vec-is-sorted-tail-is-leq-head-vec
      ( X)
      ( y ∷ (insertion-sort-vec (x ∷ z ∷ empty-vec)))
      ( is-sorting-insertion-sort-vec-helper
          ( x)
          ( z)
          ( 0)
          ( empty-vec)
          ( is-leq-or-strict-greater-total-decidable-Poset X x z)
          ( raise-star))
      ( {!!})
  is-sorting-insertion-sort-vec-helper x y (succ-ℕ (succ-ℕ n)) l (inl p) s =
    p , s
  is-sorting-insertion-sort-vec-helper x y (succ-ℕ (succ-ℕ n)) (z ∷ l) (inr p) s =
    {!!}

--   is-sorting-insertion-sort-list : is-sorting (insertion-sort-list)
--   is-sorting-insertion-sort-list nil = raise-star
--   is-sorting-insertion-sort-list (cons x nil) = raise-star
--   is-sorting-insertion-sort-list (cons x (cons y l)) =
--     is-sorting-insertion-sort-list-helper
--       ( x)
--       ( y)
--       ( insertion-sort-list l)
--       ( is-leq-or-strict-greater-total-decidable-Poset X x y)
--       {! is-sorting-insertion-sort-list !}
```

### Quick sort
