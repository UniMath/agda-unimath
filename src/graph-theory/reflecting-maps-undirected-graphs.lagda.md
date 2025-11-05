# Reflecting maps of undirected graphs

```agda
module graph-theory.reflecting-maps-undirected-graphs where
```

<details><summary>Imports</summary>

```agda
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.symmetric-identity-types
open import foundation.unit-type
open import foundation.universe-levels
open import foundation.unordered-pairs

open import graph-theory.undirected-graphs
```

</details>

## Idea

A
{{#concept "reflecting map" Disambiguation="from an undirected graph into a type" Agda=reflecting-map-Undirected-Graph}}
from an [undirected graph](graph-theory.undirected-graphs.md) `(V , E)` into a
type `X` consists of a map `fV : V → X` and a map

```text
  fE : (v : unordered-pair V) → E v → symmetric-Id (map-unordered-pair fV v).
```

In other words, it maps edges into the
[symmetric identity type](foundation.symmetric-identity-types.md).

## Definitions

### Reflecting maps of undirected graphs

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

### Terminal reflecting maps

```agda
terminal-reflecting-map-Undirected-Graph :
  {l1 l2 : Level} (G : Undirected-Graph l1 l2) →
  reflecting-map-Undirected-Graph G unit
pr1 (terminal-reflecting-map-Undirected-Graph G) x = star
pr1 (pr2 (terminal-reflecting-map-Undirected-Graph G) p e) = star
pr2 (pr2 (terminal-reflecting-map-Undirected-Graph G) p e) x =
  eq-is-contr is-contr-unit
```

## External links

- [Geometric realization](https://ncatlab.org/nlab/show/geometric+realization)
  at $n$Lab
