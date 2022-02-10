---
title: Formalisation of the Symmetry Book
---

```agda
{-# OPTIONS --without-K --exact-split --allow-unsolved-metas #-}

module graph-theory.polygons where

open import univalent-combinatorics.undirected-graphs public
open import univalent-combinatorics.finite-graphs public
```

We define the type of polygons. Our goal is show that the loop space of `Polygon k` is the dihedral group D_k.

Our definition is such that polygons are always nonempty. Accordingly, the group D_0 is the infinite dihedral group.

```agda
vertex-standard-polygon-Undirected-Graph : ℕ → UU lzero
vertex-standard-polygon-Undirected-Graph k = ℤ-Mod k

unordered-pair-vertices-standard-polygon-Undirected-Graph : ℕ → UU (lsuc lzero)
unordered-pair-vertices-standard-polygon-Undirected-Graph k =
  unordered-pair (vertex-standard-polygon-Undirected-Graph k)

edge-standard-polygon-Undirected-Graph :
  (k : ℕ) →
  unordered-pair-vertices-standard-polygon-Undirected-Graph k → UU lzero
edge-standard-polygon-Undirected-Graph k p =
  Σ ( type-unordered-pair p)
    ( λ x →
      fib
        ( element-unordered-pair p)
        ( succ-ℤ-Mod k (element-unordered-pair p x)))

is-set-vertex-standard-polygon-Undirected-Graph :
  (k : ℕ) → is-set (vertex-standard-polygon-Undirected-Graph k)
is-set-vertex-standard-polygon-Undirected-Graph k = is-set-ℤ-Mod k

module _
  (k : ℕ) (p : unordered-pair-vertices-standard-polygon-Undirected-Graph k)
  where
  
  is-emb-element-unordered-pair-edge-standard-polygon-Undirected-Graph :
    edge-standard-polygon-Undirected-Graph k p → 
    is-emb (element-unordered-pair p)
  is-emb-element-unordered-pair-edge-standard-polygon-Undirected-Graph e =
    is-emb-is-injective
      ( is-set-vertex-standard-polygon-Undirected-Graph k)
      {!!}

  is-prop-edge-standard-polygon-Undirected-Graph :
    is-prop (edge-standard-polygon-Undirected-Graph k p)
  is-prop-edge-standard-polygon-Undirected-Graph =
    {!!}

standard-polygon-Undirected-Graph : ℕ → Undirected-Graph lzero lzero
pr1 (standard-polygon-Undirected-Graph k) =
  vertex-standard-polygon-Undirected-Graph k
pr2 (standard-polygon-Undirected-Graph k) =
  edge-standard-polygon-Undirected-Graph k

Polygon : ℕ → UU (lsuc lzero)
Polygon k =
  Σ ( Undirected-Graph lzero lzero)
    ( mere-equiv-Undirected-Graph (standard-polygon-Undirected-Graph k))

module _
  (k : ℕ) (X : Polygon k)
  where
  
  undirected-graph-Polygon : Undirected-Graph lzero lzero
  undirected-graph-Polygon = pr1 X

  mere-equiv-Polygon :
    mere-equiv-Undirected-Graph
      ( standard-polygon-Undirected-Graph k)
      ( undirected-graph-Polygon)
  mere-equiv-Polygon = pr2 X

  vertex-Polygon : UU lzero
  vertex-Polygon = vertex-Undirected-Graph undirected-graph-Polygon

  unordered-pair-vertices-Polygon : UU (lsuc lzero)
  unordered-pair-vertices-Polygon = unordered-pair vertex-Polygon

  edge-Polygon : unordered-pair-vertices-Polygon → UU lzero
  edge-Polygon = edge-Undirected-Graph undirected-graph-Polygon

  mere-equiv-vertex-Polygon : mere-equiv (ℤ-Mod k) vertex-Polygon
  mere-equiv-vertex-Polygon =
    functor-trunc-Prop
      ( equiv-vertex-equiv-Undirected-Graph
        ( standard-polygon-Undirected-Graph k)
        ( undirected-graph-Polygon))
      ( mere-equiv-Polygon)

  is-finite-vertex-Polygon : is-nonzero-ℕ k → is-finite vertex-Polygon
  is-finite-vertex-Polygon H =
    is-finite-mere-equiv mere-equiv-vertex-Polygon (is-finite-ℤ-Mod H)

  is-set-vertex-Polygon : is-set vertex-Polygon
  is-set-vertex-Polygon =
    is-set-mere-equiv' mere-equiv-vertex-Polygon (is-set-ℤ-Mod k)

  has-decidable-equality-vertex-Polygon : has-decidable-equality vertex-Polygon
  has-decidable-equality-vertex-Polygon =
    has-decidable-equality-mere-equiv'
      ( mere-equiv-vertex-Polygon)
      ( has-decidable-equality-ℤ-Mod k)

  is-prop-edge-Polygon :
    (p : unordered-pair-vertices-Polygon) → is-prop (edge-Polygon p)
  is-prop-edge-Polygon p = {!!}

is-simple-standard-polygon-Undirected-Graph :
  (k : ℕ) → is-not-one-ℕ k →
  is-simple-Undirected-Graph (standard-polygon-Undirected-Graph k)
pr1 (is-simple-standard-polygon-Undirected-Graph k H) p (pair x (pair y α)) =
  is-emb-is-injective
    {!!}
    {!!}
pr2 (is-simple-standard-polygon-Undirected-Graph k H) p = {!!}
```
