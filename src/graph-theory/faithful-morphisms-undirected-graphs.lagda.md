# Faithful morphisms of undirected graphs

```agda
module graph-theory.faithful-morphisms-undirected-graphs where
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

A
{{#concept "faithful morphism" Disambiguation="of undirected graphs" Agda=is-faithful-hom-Undirected-Graph Agda=faithful-hom-Undirected-Graph}}
of [undirected graphs](graph-theory.undirected-graphs.md) is a
[morphism](graph-theory.morphisms-undirected-graphs.md) `f : G → H` of
undirected graphs such that for each
[unordered pair](foundation.unordered-pairs.md) `p` of vertices in `G` the map

```text
  edge-hom-Undirected-Graph G H f p :
    edge-Undirected-Graph G p →
    edge-Undirected-Graph H
      ( unordered-pair-vertices-hom-Undirected-Graph G H f p)
```

is an [embedding](foundation.embeddings.md).

## Definition

```agda
module _
  {l1 l2 l3 l4 : Level}
  (G : Undirected-Graph l1 l2) (H : Undirected-Graph l3 l4)
  where

  is-faithful-hom-undirected-graph-Prop :
    hom-Undirected-Graph G H → Prop (lsuc lzero ⊔ l1 ⊔ l2 ⊔ l4)
  is-faithful-hom-undirected-graph-Prop f =
    Π-Prop
      ( unordered-pair-vertices-Undirected-Graph G)
      ( λ p → is-emb-Prop (edge-hom-Undirected-Graph G H f p))

  is-faithful-hom-Undirected-Graph :
    hom-Undirected-Graph G H → UU (lsuc lzero ⊔ l1 ⊔ l2 ⊔ l4)
  is-faithful-hom-Undirected-Graph f =
    type-Prop (is-faithful-hom-undirected-graph-Prop f)

  is-prop-is-faithful-hom-Undirected-Graph :
    (f : hom-Undirected-Graph G H) →
    is-prop (is-faithful-hom-Undirected-Graph f)
  is-prop-is-faithful-hom-Undirected-Graph f =
    is-prop-type-Prop (is-faithful-hom-undirected-graph-Prop f)

  faithful-hom-Undirected-Graph : UU (lsuc lzero ⊔ l1 ⊔ l2 ⊔ l3 ⊔ l4)
  faithful-hom-Undirected-Graph =
    Σ (hom-Undirected-Graph G H) is-faithful-hom-Undirected-Graph

module _
  {l1 l2 l3 l4 : Level}
  (G : Undirected-Graph l1 l2) (H : Undirected-Graph l3 l4)
  (f : faithful-hom-Undirected-Graph G H)
  where

  hom-faithful-hom-Undirected-Graph : hom-Undirected-Graph G H
  hom-faithful-hom-Undirected-Graph = pr1 f

  is-faithful-faithful-hom-Undirected-Graph :
    is-faithful-hom-Undirected-Graph G H hom-faithful-hom-Undirected-Graph
  is-faithful-faithful-hom-Undirected-Graph = pr2 f

  vertex-faithful-hom-Undirected-Graph :
    vertex-Undirected-Graph G → vertex-Undirected-Graph H
  vertex-faithful-hom-Undirected-Graph =
    vertex-hom-Undirected-Graph G H hom-faithful-hom-Undirected-Graph

  unordered-pair-vertices-faithful-hom-Undirected-Graph :
    unordered-pair-vertices-Undirected-Graph G →
    unordered-pair-vertices-Undirected-Graph H
  unordered-pair-vertices-faithful-hom-Undirected-Graph =
    unordered-pair-vertices-hom-Undirected-Graph G H
      hom-faithful-hom-Undirected-Graph

  edge-faithful-hom-Undirected-Graph :
    (p : unordered-pair-vertices-Undirected-Graph G) →
    edge-Undirected-Graph G p →
    edge-Undirected-Graph H
      ( unordered-pair-vertices-faithful-hom-Undirected-Graph p)
  edge-faithful-hom-Undirected-Graph =
    edge-hom-Undirected-Graph G H hom-faithful-hom-Undirected-Graph

  is-emb-edge-faithful-hom-Undirected-Graph :
    (p : unordered-pair-vertices-Undirected-Graph G) →
    is-emb (edge-faithful-hom-Undirected-Graph p)
  is-emb-edge-faithful-hom-Undirected-Graph =
    is-faithful-faithful-hom-Undirected-Graph

  emb-edge-faithful-hom-Undirected-Graph :
    (p : unordered-pair-vertices-Undirected-Graph G) →
    edge-Undirected-Graph G p ↪
    edge-Undirected-Graph H
      ( unordered-pair-vertices-faithful-hom-Undirected-Graph p)
  pr1 (emb-edge-faithful-hom-Undirected-Graph p) =
    edge-faithful-hom-Undirected-Graph p
  pr2 (emb-edge-faithful-hom-Undirected-Graph p) =
    is-emb-edge-faithful-hom-Undirected-Graph p
```

## See also

- [Embeddings of undirected graphs](graph-theory.embeddings-undirected-graphs.md)
- [Totally faithful morphisms of undirected graphs](graph-theory.totally-faithful-morphisms-undirected-graphs.md)

## External links

- [Graph homomorphism](https://www.wikidata.org/entity/Q3385162) on Wikidata
- [Graph homomorphism](https://en.wikipedia.org/wiki/Graph_homomorphism) at
  Wikipedia
