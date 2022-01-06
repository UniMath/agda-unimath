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

Prepolytope : (l1 l2 : Level) → ℕ → UU {!!}
Prepolytope l1 l2 k =
  Σ ( Poset l1 l2)
    ( λ X →
      ( least-element-Poset X × largest-element-Poset X) ×
      {!!})
```
