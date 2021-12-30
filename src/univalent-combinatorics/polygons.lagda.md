---
title: Formalisation of the Symmetry Book
---

```agda
{-# OPTIONS --without-K --exact-split --allow-unsolved-metas #-}

module univalent-combinatorics.polygons where

open import univalent-combinatorics.finite-graphs public
```

We define the type of polygons. Our goal is show that the loop space of `Polygon k` is the dihedral group D_k.

```agda
polygon-Graph-𝔽 : ℕ → Graph-𝔽
Graph-𝔽.vertex (polygon-Graph-𝔽 k) = Fin-𝔽 k
Graph-𝔽.edge (polygon-Graph-𝔽 k) p =
  Σ-𝔽 ( two-element-type-𝔽 (pr1 p))
      ( λ x →
        fib-𝔽
          ( two-element-type-𝔽 (pr1 p))
          ( Fin-𝔽 k)
          ( pair-unordered-pair p)
          ( succ-Fin (pair-unordered-pair p x)))

Polygon : ℕ → UU (lsuc lzero)
Polygon k = Σ Graph-𝔽 (λ G → type-trunc-Prop (Id (polygon-Graph-𝔽 k) G))
```
