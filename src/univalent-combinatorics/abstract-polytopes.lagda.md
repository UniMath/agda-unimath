---
title: Formalisation of the Symmetry Book
---

```agda
{-# OPTIONS --without-K --exact-split --allow-unsolved-metas #-}

module univalent-combinatorics.abstract-polytopes where

open import order-theory public
```

## Axiom P1 of polytopes

The first axiom of polytopes asserts that polytopes have a least and a largest element.

```agda

module _
  {l1 l2 : Level} (k : ℕ) (X : Finitely-Graded-Poset l1 l2 k)
  where

  P1-Polytope-Prop : UU-Prop (l1 ⊔ l2)
  P1-Polytope-Prop =
    prod-Prop
      ( least-element-Finitely-Graded-Poset-Prop X)
      ( largest-element-Finitely-Graded-Poset-Prop X)

  P1-Polytope : UU (l1 ⊔ l2)
  P1-Polytope = type-Prop P1-Polytope-Prop

  is-prop-P1-Polytope : is-prop P1-Polytope
  is-prop-P1-Polytope = is-prop-type-Prop P1-Polytope-Prop
```

## Axiom P2 of polytopes

The second axiom of polytopes asserts that every maximal chain has k elements. Here, the natural number k is the rank of the polytope. In classical mathematics, this axiom implies that the underlying poset of a polytope is graded. Here, we will assume that polytopes come equipped with a grading.

  (P2') The poset X is graded, and the maximal chains in X have exactly (k + 1) elements.

```agda
module _
  {l1 l2 : Level} (l3 : Level) (k : ℕ) (X : Finitely-Graded-Poset l1 l2 k)
  where

```

  (P4) We state the diamond condition

```agda

diamond-condition-Finitely-Graded-Poset :
  {l1 l2 : Level} (k : ℕ) (X : Finitely-Graded-Poset l1 l2 k) →
  UU-Prop (l1 ⊔ l2)
diamond-condition-Finitely-Graded-Poset zero-ℕ X = raise-unit-Prop _
diamond-condition-Finitely-Graded-Poset (succ-ℕ k) X =
  Π-Prop
    ( Fin k)
    ( λ i →
      Π-Prop
        ( face-Finitely-Graded-Poset X (inl-Fin (succ-ℕ k) (inl-Fin k i)))
        ( λ x →
          Π-Prop
            ( face-Finitely-Graded-Poset X
              ( succ-Fin (succ-Fin (inl-Fin (succ-ℕ k) (inl-Fin k i)))))
            ( λ y →
              has-cardinality-Prop
                ( Σ ( face-Finitely-Graded-Poset X
                      ( succ-Fin (inl-Fin (succ-ℕ k) (inl-Fin k i))))
                    ( λ z →
                      adjacent-Finitely-Graded-Poset X (inl-Fin k i) x z ×
                      adjacent-Finitely-Graded-Poset X
                        ( succ-Fin (inl-Fin k i))
                        ( z)
                        ( y)))
                ( two-ℕ))))
  
  
--   P2-Polytope-Prop : UU-Prop (l1 ⊔ l2 ⊔ lsuc l3)
--   P2-Polytope-Prop =
--     Π-Prop
--       ( maximal-chain-Finitely-Graded-Poset l3 X)
--       ( λ C → has-cardinality-Prop (element-maximal-chain-Finitely-Graded-Poset X C) (succ-ℕ k))

--   P2-Polytope : UU (l1 ⊔ l2 ⊔ lsuc l3)
--   P2-Polytope = type-Prop P2-Polytope-Prop

--   is-prop-P2-Polytope : is-prop P2-Polytope
--   is-prop-P2-Polytope = is-prop-type-Prop P2-Polytope-Prop

-- Prepolytope : (l1 l2 l3 : Level) → ℕ → UU (lsuc l1 ⊔ lsuc l2 ⊔ lsuc l3)
-- Prepolytope l1 l2 l3 k =
--   Σ ( Finitely-Graded-Poset l1 l2) (λ X → P1-Polytope X × P2-Polytope l3 k X)

-- module _
--   {l1 l2 l3 : Level} (k : ℕ) (X : Prepolytope l1 l2 l3 k)
--   where

--   poset-Prepolytope : Finitely-Graded-Poset l1 l2
--   poset-Prepolytope = pr1 X

--   P1-polytope-Prepolytope : P1-Polytope poset-Prepolytope
--   P1-polytope-Prepolytope = pr1 (pr2 X)

--   P2-polytope-Prepolytope : P2-Polytope l3 k poset-Prepolytope
--   P2-polytope-Prepolytope = pr2 (pr2 X)

--   face-set-Prepolytope : UU l1
--   face-set-Prepolytope = element-Finitely-Graded-Poset poset-Prepolytope

--   is-set-face-set-Prepolytope : is-set face-set-Prepolytope
--   is-set-face-set-Prepolytope = is-set-element-Finitely-Graded-Poset poset-Prepolytope

--   face-set-Prepolytope-Set : UU-Set l1
--   face-set-Prepolytope-Set = element-poset-Set poset-Prepolytope
-- ```

-- ### The diamond condition

-- ```agda
