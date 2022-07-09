# Orientations of undirected graphs

```agda
{-# OPTIONS --without-K --exact-split #-}

module graph-theory.orientations-undirected-graphs where

open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.universe-levels using (Level; UU; _⊔_; lsuc; lzero)

open import graph-theory.undirected-graphs using
  ( Undirected-Graph; unordered-pair-vertices-Undirected-Graph;
    edge-Undirected-Graph; vertex-Undirected-Graph)

open import univalent-combinatorics.finite-types using (type-UU-Fin)
```

## Idea

An orientation of an undirected graph is a function that picks a direction for every edge.

## Definition

```agda
module _
  {l1 l2 : Level} (G : Undirected-Graph l1 l2)
  where

  orientation-Undirected-Graph : UU (lsuc lzero ⊔ l1 ⊔ l2)
  orientation-Undirected-Graph =
    ( p : unordered-pair-vertices-Undirected-Graph G) →
    edge-Undirected-Graph G p → type-UU-Fin 2 (pr1 p)

  source-edge-orientation-Undirected-Graph :
    orientation-Undirected-Graph →
    (p : unordered-pair-vertices-Undirected-Graph G) →
    edge-Undirected-Graph G p → vertex-Undirected-Graph G
  source-edge-orientation-Undirected-Graph d (pair X p) e =
    p (d (pair X p) e)
```
