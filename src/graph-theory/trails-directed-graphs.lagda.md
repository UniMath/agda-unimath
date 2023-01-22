---
title: Trails in directed graphs
---

```agda
module graph-theory.trails-directed-graphs where

open import foundation.dependent-pair-types
open import foundation.injective-maps
open import foundation.universe-levels

open import graph-theory.directed-graphs
open import graph-theory.walks-directed-graphs
```

## Idea

A trail in a directed graph is a walk that goes through each edge at most once.

```agda
module _
  {l1 l2 : Level} (G : Graph l1 l2)
  where
  
  is-trail-walk-Graph :
    {x y : vertex-Graph G} (w : walk-Graph G x y) → UU (l1 ⊔ l2)
  is-trail-walk-Graph w = is-injective (total-edge-edge-on-walk-Graph G w)

  trail-Graph : (x y : vertex-Graph G) → UU (l1 ⊔ l2)
  trail-Graph x y = Σ (walk-Graph G x y) (is-trail-walk-Graph)

  walk-trail-Graph : {x y : vertex-Graph G} → trail-Graph x y → walk-Graph G x y
  walk-trail-Graph = pr1

  is-trail-trail-Graph :
    {x y : vertex-Graph G} (t : trail-Graph x y) →
    is-trail-walk-Graph (walk-trail-Graph t)
  is-trail-trail-Graph = pr2
```
