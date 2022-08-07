---
title: Trees
---

```agda
module graph-theory.trees where

open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import graph-theory.trails-undirected-graphs
open import graph-theory.undirected-graphs
```

## Idea

A tree is a graph such that the type of trails from x to y is contractible for any two vertices x and y.

## Definition

```agda
is-tree-Undirected-Graph :
  {l1 l2 : Level} (G : Undirected-Graph l1 l2) → UU (lsuc lzero ⊔ l1 ⊔ l2)
is-tree-Undirected-Graph G =
  (x y : vertex-Undirected-Graph G) → is-contr (trail-Undirected-Graph G x y)

Tree : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
Tree l1 l2 = Σ (Undirected-Graph l1 l2) is-tree-Undirected-Graph

module _
  {l1 l2 : Level} (T : Tree l1 l2)
  where

  undirected-graph-Tree : Undirected-Graph l1 l2
  undirected-graph-Tree = pr1 T

  node-Tree : UU l1
  node-Tree = vertex-Undirected-Graph undirected-graph-Tree

  trail-Tree :
    (x y : node-Tree) → trail-Undirected-Graph undirected-graph-Tree x y
  trail-Tree x y = center (pr2 T x y)
```
