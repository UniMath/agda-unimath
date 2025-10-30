# Embeddings of undirected graphs

```agda
module graph-theory.embeddings-undirected-graphs where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.propositions
open import foundation.universe-levels

open import graph-theory.morphisms-undirected-graphs
open import graph-theory.undirected-graphs
```

</details>

## Idea

An
{{#concept "embedding" Disambiguation="of undirected graphs" Agda=is-emb-Undirected-Graph Agda=emb-Undirected-Graph}}
of [undirected graphs](graph-theory.undirected-graphs.md) is a
[morphism](graph-theory.morphisms-undirected-graphs.md) `f : G → H` of
undirected graphs which is an [embedding](foundation.embeddings.md) on vertices
such that for each [unordered pair](foundation.unordered-pairs.md) `p` of
vertices in `G` the map

```text
  edge-hom-Undirected-Graph G H :
    edge-Undirected-Graph G p →
    edge-Undirected-Graph H (unordered-pair-vertices-hom-Undirected-Graph G H f)
```

is also an embedding. Embeddings of undirected graphs correspond to undirected
subgraphs.

**Note:** Our notion of embeddings of directed graphs differs quite
substantially from the graph theoretic notion of _graph embedding_, which
usually refers to an embedding of a graph into the plane.

## Definition

```agda
module _
  {l1 l2 l3 l4 : Level}
  (G : Undirected-Graph l1 l2) (H : Undirected-Graph l3 l4)
  where

  is-emb-hom-undirected-graph-Prop :
    hom-Undirected-Graph G H → Prop (lsuc lzero ⊔ l1 ⊔ l2 ⊔ l3 ⊔ l4)
  is-emb-hom-undirected-graph-Prop f =
    product-Prop
      ( is-emb-Prop (vertex-hom-Undirected-Graph G H f))
      ( Π-Prop
        ( unordered-pair-vertices-Undirected-Graph G)
        ( λ p →
          is-emb-Prop (edge-hom-Undirected-Graph G H f p)))

  is-emb-hom-Undirected-Graph :
    hom-Undirected-Graph G H → UU (lsuc lzero ⊔ l1 ⊔ l2 ⊔ l3 ⊔ l4)
  is-emb-hom-Undirected-Graph f = type-Prop (is-emb-hom-undirected-graph-Prop f)

  is-prop-is-emb-hom-Undirected-Graph :
    (f : hom-Undirected-Graph G H) → is-prop (is-emb-hom-Undirected-Graph f)
  is-prop-is-emb-hom-Undirected-Graph f =
    is-prop-type-Prop (is-emb-hom-undirected-graph-Prop f)

  emb-Undirected-Graph : UU (lsuc lzero ⊔ l1 ⊔ l2 ⊔ l3 ⊔ l4)
  emb-Undirected-Graph =
    Σ (hom-Undirected-Graph G H) is-emb-hom-Undirected-Graph

module _
  {l1 l2 l3 l4 : Level}
  (G : Undirected-Graph l1 l2) (H : Undirected-Graph l3 l4)
  (f : emb-Undirected-Graph G H)
  where

  hom-emb-Undirected-Graph : hom-Undirected-Graph G H
  hom-emb-Undirected-Graph = pr1 f

  is-emb-emb-Undirected-Graph :
    is-emb-hom-Undirected-Graph G H hom-emb-Undirected-Graph
  is-emb-emb-Undirected-Graph = pr2 f

  vertex-emb-Undirected-Graph :
    vertex-Undirected-Graph G → vertex-Undirected-Graph H
  vertex-emb-Undirected-Graph =
    vertex-hom-Undirected-Graph G H hom-emb-Undirected-Graph

  is-emb-vertex-emb-Undirected-Graph :
    is-emb vertex-emb-Undirected-Graph
  is-emb-vertex-emb-Undirected-Graph = pr1 is-emb-emb-Undirected-Graph

  emb-vertex-emb-Undirected-Graph :
    vertex-Undirected-Graph G ↪ vertex-Undirected-Graph H
  pr1 emb-vertex-emb-Undirected-Graph = vertex-emb-Undirected-Graph
  pr2 emb-vertex-emb-Undirected-Graph = is-emb-vertex-emb-Undirected-Graph

  unordered-pair-vertices-emb-Undirected-Graph :
    unordered-pair-vertices-Undirected-Graph G →
    unordered-pair-vertices-Undirected-Graph H
  unordered-pair-vertices-emb-Undirected-Graph =
    unordered-pair-vertices-hom-Undirected-Graph G H hom-emb-Undirected-Graph

  edge-emb-Undirected-Graph :
    (p : unordered-pair-vertices-Undirected-Graph G) →
    edge-Undirected-Graph G p →
    edge-Undirected-Graph H (unordered-pair-vertices-emb-Undirected-Graph p)
  edge-emb-Undirected-Graph =
    edge-hom-Undirected-Graph G H hom-emb-Undirected-Graph

  is-emb-edge-emb-Undirected-Graph :
    (p : unordered-pair-vertices-Undirected-Graph G) →
    is-emb (edge-emb-Undirected-Graph p)
  is-emb-edge-emb-Undirected-Graph = pr2 is-emb-emb-Undirected-Graph

  emb-edge-emb-Undirected-Graph :
    (p : unordered-pair-vertices-Undirected-Graph G) →
    edge-Undirected-Graph G p ↪
    edge-Undirected-Graph H (unordered-pair-vertices-emb-Undirected-Graph p)
  pr1 (emb-edge-emb-Undirected-Graph p) = edge-emb-Undirected-Graph p
  pr2 (emb-edge-emb-Undirected-Graph p) = is-emb-edge-emb-Undirected-Graph p
```

## See also

- [Faithful morphisms of undirected graphs](graph-theory.faithful-morphisms-undirected-graphs.md)
- [Totally faithful morphisms of undirected graphs](graph-theory.totally-faithful-morphisms-undirected-graphs.md)

## External links

- [Graph homomorphism](https://www.wikidata.org/entity/Q3385162) on Wikidata
- [Graph homomorphism](https://en.wikipedia.org/wiki/Graph_homomorphism) on
  Wikipedia
