# Raising universe levels of directed graphs

```agda
module graph-theory.raising-universe-levels-directed-graphs where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.raising-universe-levels
open import foundation.universe-levels

open import graph-theory.directed-graphs
open import graph-theory.equivalences-directed-graphs
open import graph-theory.walks-directed-graphs
```

</details>

## Idea

We
{{#concept "raise" Disambiguation="the universe levels of directed graphs" Agda=raise-Directed-Graph}}
the [universe levels](foundation.universe-levels.md) of
[directed graphs](graph-theory.directed-graphs.md) by
[raising the universe levels](foundation.raising-universe-levels.md) of the
vertices and the edges.

## Definition

```agda
module _
  {l1 l2 : Level} (l3 l4 : Level) (G : Directed-Graph l1 l2)
  where

  vertex-raise-Directed-Graph : UU (l1 ⊔ l3)
  vertex-raise-Directed-Graph = raise l3 (vertex-Directed-Graph G)

  vertex-equiv-compute-raise-Directed-Graph :
    vertex-Directed-Graph G ≃ vertex-raise-Directed-Graph
  vertex-equiv-compute-raise-Directed-Graph =
    compute-raise l3 (vertex-Directed-Graph G)

  vertex-compute-raise-Directed-Graph :
    vertex-Directed-Graph G → vertex-raise-Directed-Graph
  vertex-compute-raise-Directed-Graph =
    map-equiv vertex-equiv-compute-raise-Directed-Graph

  edge-raise-Directed-Graph :
    (x y : vertex-raise-Directed-Graph) → UU (l2 ⊔ l4)
  edge-raise-Directed-Graph (map-raise x) (map-raise y) =
    raise l4 (edge-Directed-Graph G x y)

  edge-equiv-compute-raise-Directed-Graph :
    (x y : vertex-Directed-Graph G) →
    edge-Directed-Graph G x y ≃
    edge-raise-Directed-Graph
      ( vertex-compute-raise-Directed-Graph x)
      ( vertex-compute-raise-Directed-Graph y)
  edge-equiv-compute-raise-Directed-Graph x y =
    compute-raise l4 (edge-Directed-Graph G x y)

  edge-compute-raise-Directed-Graph :
    (x y : vertex-Directed-Graph G) →
    edge-Directed-Graph G x y →
    edge-raise-Directed-Graph
      ( vertex-compute-raise-Directed-Graph x)
      ( vertex-compute-raise-Directed-Graph y)
  edge-compute-raise-Directed-Graph x y =
    map-equiv (edge-equiv-compute-raise-Directed-Graph x y)

  raise-Directed-Graph : Directed-Graph (l1 ⊔ l3) (l2 ⊔ l4)
  pr1 raise-Directed-Graph = vertex-raise-Directed-Graph
  pr2 raise-Directed-Graph = edge-raise-Directed-Graph

  compute-raise-Directed-Graph :
    equiv-Directed-Graph G raise-Directed-Graph
  pr1 compute-raise-Directed-Graph = vertex-equiv-compute-raise-Directed-Graph
  pr2 compute-raise-Directed-Graph = edge-equiv-compute-raise-Directed-Graph

  walk-raise-Directed-Graph :
    (x y : vertex-raise-Directed-Graph) → UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  walk-raise-Directed-Graph = walk-Directed-Graph raise-Directed-Graph

  equiv-walk-compute-raise-Directed-Graph :
    {x y : vertex-Directed-Graph G} →
    walk-Directed-Graph G x y ≃
    walk-raise-Directed-Graph
      ( vertex-compute-raise-Directed-Graph x)
      ( vertex-compute-raise-Directed-Graph y)
  equiv-walk-compute-raise-Directed-Graph =
    equiv-walk-equiv-Directed-Graph G
      raise-Directed-Graph
      compute-raise-Directed-Graph

  walk-compute-raise-Directed-Graph :
    {x y : vertex-Directed-Graph G} →
    walk-Directed-Graph G x y →
    walk-raise-Directed-Graph
      ( vertex-compute-raise-Directed-Graph x)
      ( vertex-compute-raise-Directed-Graph y)
  walk-compute-raise-Directed-Graph =
    map-equiv equiv-walk-compute-raise-Directed-Graph
```
