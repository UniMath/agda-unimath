---
title: Enriched undirected graphs
---

```agda
module graph-theory.enriched-undirected-graphs where

open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.universe-levels

open import graph-theory.neighbors-undirected-graphs
open import graph-theory.undirected-graphs
```

## Idea

Consider a type `A` equipped with a type family `B` over `A`. An **`(A,B)`-enriched undirected graph** is an undirected graph `G := (V,E)` equipped with a map `f : V → A`, and for each vertex `v` an equivalence from `B (f v)` to the type of all vertices `w` equipped with an edge between `v` and `w`.

## Definition

```agda 
Enriched-Undirected-Graph :
  {l1 l2 : Level} (l3 l4 : Level) (A : UU l1) (B : A → UU l2) →
  UU (l1 ⊔ l2 ⊔ lsuc l3 ⊔ lsuc l4)
Enriched-Undirected-Graph l3 l4 A B =
  Σ ( Undirected-Graph l3 l4)
    ( λ G →
      Σ ( vertex-Undirected-Graph G → A)
        ( λ f →
          ( x : vertex-Undirected-Graph G) →
          B (f x) ≃ neighbor-Undirected-Graph G x))

module _
  {l1 l2 l3 l4 : Level} (A : UU l1) (B : A → UU l2)
  (G : Enriched-Undirected-Graph l3 l4 A B)
  where

  undirected-graph-Enriched-Undirected-Graph : Undirected-Graph l3 l4
  undirected-graph-Enriched-Undirected-Graph = pr1 G

  vertex-Enriched-Undirected-Graph : UU l3
  vertex-Enriched-Undirected-Graph =
    vertex-Undirected-Graph undirected-graph-Enriched-Undirected-Graph

  unordered-pair-vertices-Enriched-Undirected-Graph : UU (lsuc lzero ⊔ l3)
  unordered-pair-vertices-Enriched-Undirected-Graph =
    unordered-pair-vertices-Undirected-Graph undirected-graph-Enriched-Undirected-Graph

  edge-Enriched-Undirected-Graph :
    unordered-pair-vertices-Enriched-Undirected-Graph → UU l4
  edge-Enriched-Undirected-Graph =
    edge-Undirected-Graph undirected-graph-Enriched-Undirected-Graph

  label-vertex-Enriched-Undirected-Graph : vertex-Enriched-Undirected-Graph → A
  label-vertex-Enriched-Undirected-Graph = pr1 (pr2 G)

  neighbor-Enriched-Undirected-Graph :
    vertex-Enriched-Undirected-Graph → UU (l3 ⊔ l4)
  neighbor-Enriched-Undirected-Graph =
    neighbor-Undirected-Graph undirected-graph-Enriched-Undirected-Graph

  equiv-neighbor-Enriched-Undirected-Graph :
    (x : vertex-Enriched-Undirected-Graph) →
    B (label-vertex-Enriched-Undirected-Graph x) ≃
    neighbor-Enriched-Undirected-Graph x
  equiv-neighbor-Enriched-Undirected-Graph = pr2 (pr2 G)

  map-equiv-neighbor-Enriched-Undirected-Graph :
    (x : vertex-Enriched-Undirected-Graph) →
    B (label-vertex-Enriched-Undirected-Graph x) → neighbor-Enriched-Undirected-Graph x
  map-equiv-neighbor-Enriched-Undirected-Graph x =
    map-equiv (equiv-neighbor-Enriched-Undirected-Graph x)
```
