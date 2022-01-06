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
  {l1 l2 : Level} (X : Poset l1 l2)
  where

  P1-Polytope-Prop : UU-Prop (l1 ⊔ l2)
  P1-Polytope-Prop =
    prod-Prop
      ( has-least-element-Poset-Prop X)
      ( has-largest-element-Poset-Prop X)

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
  {l1 l2 : Level} (l3 : Level) (k : ℕ) (X : Poset l1 l2)
  where
  
  P2-Polytope-Prop : UU-Prop (l1 ⊔ l2 ⊔ lsuc l3)
  P2-Polytope-Prop =
    Π-Prop
      ( maximal-chain-Poset l3 X)
      ( λ C → has-cardinality-Prop (element-maximal-chain-Poset X C) (succ-ℕ k))

  P2-Polytope : UU (l1 ⊔ l2 ⊔ lsuc l3)
  P2-Polytope = type-Prop P2-Polytope-Prop

  is-prop-P2-Polytope : is-prop P2-Polytope
  is-prop-P2-Polytope = is-prop-type-Prop P2-Polytope-Prop

Prepolytope : (l1 l2 l3 : Level) → ℕ → UU (lsuc l1 ⊔ lsuc l2 ⊔ lsuc l3)
Prepolytope l1 l2 l3 k =
  Σ ( Poset l1 l2) (λ X → P1-Polytope X × P2-Polytope l3 k X)

module _
  {l1 l2 l3 : Level} (k : ℕ) (X : Prepolytope l1 l2 l3 k)
  where

  poset-Prepolytope : Poset l1 l2
  poset-Prepolytope = pr1 X

  P1-polytope-Prepolytope : P1-Polytope poset-Prepolytope
  P1-polytope-Prepolytope = pr1 (pr2 X)

  P2-polytope-Prepolytope : P2-Polytope l3 k poset-Prepolytope
  P2-polytope-Prepolytope = pr2 (pr2 X)

  face-set-Prepolytope : UU l1
  face-set-Prepolytope = element-Poset poset-Prepolytope

  is-set-face-set-Prepolytope : is-set face-set-Prepolytope
  is-set-face-set-Prepolytope = is-set-element-Poset poset-Prepolytope

  face-set-Prepolytope-Set : UU-Set l1
  face-set-Prepolytope-Set = element-poset-Set poset-Prepolytope
```
