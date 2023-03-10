# Reflecting maps of undirected graphs

```agda
module graph-theory.reflecting-maps-undirected-graphs where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.symmetric-identity-types
open import foundation.universe-levels
open import foundation.unordered-pairs

open import graph-theory.undirected-graphs
```

</details>

## Idea

A reflecting map from an undirected graph `(V , E)` into a type `X` consists of a map `fV : V → X` and a map

```md
  fE : (v : unordered-pair V) → E v → symmetric-Id (map-unordered-pair fV v).
```

In other words, it maps edges into the symmetric identity type.

## Definition

```agda
reflecting-map-Undirected-Graph :
  {l1 l2 l3 : Level} (G : Undirected-Graph l1 l2) (X : UU l3) →
  UU (lsuc lzero ⊔ l1 ⊔ l2 ⊔ l3)
reflecting-map-Undirected-Graph G X =
  Σ ( vertex-Undirected-Graph G → X)
    ( λ f →
      (v : unordered-pair-vertices-Undirected-Graph G) →
      edge-Undirected-Graph G v → symmetric-Id (map-unordered-pair f v))

module _
  {l1 l2 l3 : Level} (G : Undirected-Graph l1 l2) {X : UU l3}
  (f : reflecting-map-Undirected-Graph G X)
  where

  vertex-reflecting-map-Undirected-Graph : vertex-Undirected-Graph G → X
  vertex-reflecting-map-Undirected-Graph = pr1 f

  unordered-pair-vertices-reflecting-map-Undirected-Graph :
    unordered-pair-vertices-Undirected-Graph G → unordered-pair X
  unordered-pair-vertices-reflecting-map-Undirected-Graph =
    map-unordered-pair vertex-reflecting-map-Undirected-Graph

  edge-reflecting-map-Undirected-Graph :
    (v : unordered-pair-vertices-Undirected-Graph G) →
    edge-Undirected-Graph G v →
    symmetric-Id (unordered-pair-vertices-reflecting-map-Undirected-Graph v)
  edge-reflecting-map-Undirected-Graph = pr2 f
```
