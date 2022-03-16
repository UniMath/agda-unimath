# Connected graphs

```agda
{-# OPTIONS --without-K --exact-split #-}

module graph-theory.connected-undirected-graphs where

open import foundation.propositional-truncations using (type-trunc-Prop)
open import foundation.universe-levels using (Level; UU; _⊔_; lsuc; lzero)

open import graph-theory.paths-undirected-graphs using
  ( path-Undirected-Graph)
open import graph-theory.undirected-graphs using
  ( Undirected-Graph; vertex-Undirected-Graph)
```

## Idea

A graph is said to be connected if any point can be reached from any point by a path of edges

## Definition

```agda
module _
  {l1 l2 : Level} (G : Undirected-Graph l1 l2)
  where

  is-connected-undirected-graph : UU (l1 ⊔ l2 ⊔ lsuc lzero)
  is-connected-undirected-graph =
    (x y : vertex-Undirected-Graph G) →
    type-trunc-Prop (path-Undirected-Graph G x y)
```
