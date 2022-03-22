# Paths in undirected graphs

```agda
{-# OPTIONS --without-K --exact-split #-}

module graph-theory.paths-undirected-graphs where

open import foundation.universe-levels using (Level; UU; _⊔_; lsuc; lzero)
open import foundation.unordered-pairs using
  ( unordered-pair; type-unordered-pair; element-unordered-pair;
    other-element-unordered-pair)

open import graph-theory.undirected-graphs using
  ( Undirected-Graph; vertex-Undirected-Graph; edge-Undirected-Graph)
```

## Idea

A path in an undirected graph consists of a list of edges that connect the starting point with the end point

```agda
-- TODO: I would rather use the notion of a walk, as a path is often a walk without repeated vertices.

module _
  {l1 l2 : Level} (G : Undirected-Graph l1 l2)
  where

  data
    path-Undirected-Graph (x : vertex-Undirected-Graph G) :
      vertex-Undirected-Graph G → UU (l1 ⊔ l2 ⊔ lsuc lzero)
      where
      refl-path-Undirected-Graph : path-Undirected-Graph x x
      cons-path-Undirected-Graph :
        (p : unordered-pair (vertex-Undirected-Graph G)) →
        (e : edge-Undirected-Graph G p) →
        {y : type-unordered-pair p} →
        path-Undirected-Graph x (element-unordered-pair p y) →
        path-Undirected-Graph x (other-element-unordered-pair p y)
```
