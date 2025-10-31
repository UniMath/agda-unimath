# Incidence in undirected graphs

```agda
module graph-theory.neighbors-undirected-graphs where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.equality-dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.universe-levels
open import foundation.unordered-pairs

open import graph-theory.equivalences-undirected-graphs
open import graph-theory.undirected-graphs
```

</details>

## Idea

The type of
{{#concept "neighbors" Disambiguation="of a vertex of an undirected graph" Agda=neighbor-Undirected-Graph}}
of a vertex `x` of an [undirected graph](graph-theory.undirected-graphs.md) `G`
is the type of all vertices `y` in `G` equipped with an edge from `x` to `y`.

## Definition

```agda
module _
  {l1 l2 : Level} (G : Undirected-Graph l1 l2)
  where

  neighbor-Undirected-Graph : vertex-Undirected-Graph G → UU (l1 ⊔ l2)
  neighbor-Undirected-Graph x =
    Σ ( vertex-Undirected-Graph G)
      ( λ y → edge-Undirected-Graph G (standard-unordered-pair x y))
```

## Properties

### Equivalences of undirected graphs induce equivalences on types of neighbors

```agda
module _
  {l1 l2 l3 l4 : Level}
  (G : Undirected-Graph l1 l2) (H : Undirected-Graph l3 l4)
  where

  equiv-neighbor-equiv-Undirected-Graph :
    (e : equiv-Undirected-Graph G H) (x : vertex-Undirected-Graph G) →
    neighbor-Undirected-Graph G x ≃
    neighbor-Undirected-Graph H (vertex-equiv-Undirected-Graph G H e x)
  equiv-neighbor-equiv-Undirected-Graph e x =
    equiv-Σ
      ( λ y →
        edge-Undirected-Graph H
          ( standard-unordered-pair (vertex-equiv-Undirected-Graph G H e x) y))
      ( vertex-equiv-equiv-Undirected-Graph G H e)
      ( edge-equiv-standard-unordered-pair-vertices-equiv-Undirected-Graph
          G H e x)

  neighbor-equiv-Undirected-Graph :
    (e : equiv-Undirected-Graph G H) (x : vertex-Undirected-Graph G) →
    neighbor-Undirected-Graph G x →
    neighbor-Undirected-Graph H (vertex-equiv-Undirected-Graph G H e x)
  neighbor-equiv-Undirected-Graph e x =
    map-equiv (equiv-neighbor-equiv-Undirected-Graph e x)

neighbor-id-equiv-Undirected-Graph :
  {l1 l2 : Level}
  (G : Undirected-Graph l1 l2) (x : vertex-Undirected-Graph G) →
  neighbor-equiv-Undirected-Graph G G (id-equiv-Undirected-Graph G) x ~ id
neighbor-id-equiv-Undirected-Graph G x (pair y e) =
  eq-pair-eq-fiber
    ( edge-standard-unordered-pair-vertices-id-equiv-Undirected-Graph G x y e)
```

## External links

- [Neighborhood](https://www.wikidata.org/entity/Q1354987) on Wikidata
- [Neighborhood (graph theory)](<https://en.wikipedia.org/wiki/Neighbourhood_(graph_theory)>)
  at Wikipedia
- [Graph neighborhood](https://mathworld.wolfram.com/GraphNeighborhood.html) at
  Wolfram MathWorld
