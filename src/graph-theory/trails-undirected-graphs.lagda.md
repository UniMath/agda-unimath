---
title: Trails in undirected graphs
---

```agda
module graph-theory.trails-undirected-graphs where

open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.injective-maps
open import foundation.universe-levels

open import graph-theory.undirected-graphs
open import graph-theory.walks-undirected-graphs
```

## Idea

A trail in an undirected graph is a walk that passes through each edge at most once

## Definition

```agda
module _
  {l1 l2 : Level} (G : Undirected-Graph l1 l2)
  where
  
  is-trail-walk-Undirected-Graph :
    {x y : vertex-Undirected-Graph G} → walk-Undirected-Graph G x y →
    UU (lsuc lzero ⊔ l1 ⊔ l2)
  is-trail-walk-Undirected-Graph w =
    is-injective (edge-edge-on-walk-Undirected-Graph G w)

  trail-Undirected-Graph :
    (x y : vertex-Undirected-Graph G) → UU (lsuc lzero ⊔ l1 ⊔ l2)
  trail-Undirected-Graph x y =
    Σ (walk-Undirected-Graph G x y) is-trail-walk-Undirected-Graph

  walk-trail-Undirected-Graph :
    {x y : vertex-Undirected-Graph G} →
    trail-Undirected-Graph x y → walk-Undirected-Graph G x y
  walk-trail-Undirected-Graph = pr1

  length-trail-Undirected-Graph :
    {x y : vertex-Undirected-Graph G} → trail-Undirected-Graph x y → ℕ
  length-trail-Undirected-Graph t =
    length-walk-Undirected-Graph G (walk-trail-Undirected-Graph t)
```
