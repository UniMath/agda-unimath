---
title: Formalisation of the Symmetry Book
---

```agda
{-# OPTIONS --without-K --exact-split --allow-unsolved-metas #-}

module univalent-combinatorics.abstract-polytopes where

open import order-theory public
```

## Posets satisfying axioms P1 and P2 of abstract polytopes

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
  Σ ( Poset l1 l2) (λ X → (P1-Polytope X) × (P2-Polytope l3 k X))
```
