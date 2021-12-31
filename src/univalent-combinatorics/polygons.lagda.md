---
title: Formalisation of the Symmetry Book
---

```agda
{-# OPTIONS --without-K --exact-split --allow-unsolved-metas #-}

module univalent-combinatorics.polygons where

open import univalent-combinatorics.graphs public
open import univalent-combinatorics.finite-graphs public
```

We define the type of polygons. Our goal is show that the loop space of `Polygon k` is the dihedral group D_k.

Our definition is such that polygons are always nonempty. Accordingly, the group D_0 is the infinite dihedral group.

```agda
polygon-Undirected-Graph : ℕ → Undirected-Graph lzero lzero
pr1 (polygon-Undirected-Graph k) = ℤ-Mod k
pr2 (polygon-Undirected-Graph k) p =
  Σ ( type-unordered-pair p)
    ( λ x →
      fib
        ( element-unordered-pair p)
        ( succ-ℤ-Mod k (element-unordered-pair p x)))

Polygon : ℕ → UU (lsuc lzero)
Polygon k =
  Σ ( Undirected-Graph lzero lzero)
    ( λ G → type-trunc-Prop (Id (polygon-Undirected-Graph k) G))

is-simple-polygon-Undirected-Graph :
  (k : ℕ) → is-not-one-ℕ k →
  is-simple-Undirected-Graph (polygon-Undirected-Graph k)
pr1 (is-simple-polygon-Undirected-Graph k H) p (pair x (pair y α)) = {!!}
pr2 (is-simple-polygon-Undirected-Graph k H) = {!!}
```
