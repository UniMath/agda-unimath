# Trails in directed graphs

```agda
module graph-theory.trails-directed-graphs where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.injective-maps
open import foundation.universe-levels

open import graph-theory.directed-graphs
open import graph-theory.walks-directed-graphs
```

</details>

## Idea

A trail in a directed graph is a walk that goes through each edge at most once.

```agda
module _
  {l1 l2 : Level} (G : Directed-Graph l1 l2)
  where

  is-trail-walk-Directed-Graph :
    {x y : vertex-Directed-Graph G} → walk-Directed-Graph G x y → UU (l1 ⊔ l2)
  is-trail-walk-Directed-Graph w =
    is-injective (total-edge-edge-on-walk-Directed-Graph G w)

  trail-Directed-Graph : (x y : vertex-Directed-Graph G) → UU (l1 ⊔ l2)
  trail-Directed-Graph x y =
    Σ (walk-Directed-Graph G x y) (is-trail-walk-Directed-Graph)

  walk-trail-Directed-Graph :
    {x y : vertex-Directed-Graph G} →
    trail-Directed-Graph x y → walk-Directed-Graph G x y
  walk-trail-Directed-Graph = pr1

  is-trail-trail-Directed-Graph :
    {x y : vertex-Directed-Graph G} (t : trail-Directed-Graph x y) →
    is-trail-walk-Directed-Graph (walk-trail-Directed-Graph t)
  is-trail-trail-Directed-Graph = pr2
```
