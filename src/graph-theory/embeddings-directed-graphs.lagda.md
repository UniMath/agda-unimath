# Embeddings of directed graphs

```agda
module graph-theory.embeddings-directed-graphs where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.propositions
open import foundation.universe-levels

open import graph-theory.directed-graphs
open import graph-theory.morphisms-directed-graphs
```

</details>

## Idea

An
{{#concept "embedding" Disambiguation="of directed graphs" Agda=is-emb-hom-Directed-Graph Agda=emb-Directed-Graph}}
of [directed graphs](graph-theory.directed-graphs.md) is a
[morphism](graph-theory.morphisms-directed-graphs.md) of directed graphs
`f : G → H` which is an [embedding](foundation.embeddings.md) on vertices such
that for each pair `(x , y)` of vertices in `G` the map

```text
  edge-hom-Graph G H : edge-Graph G p → edge-Graph H x y
```

is also an embedding. Embeddings of directed graphs correspond to directed
subgraphs.

**Note:** Our notion of embeddings of directed graphs differs quite
substantially from the graph theoretic notion of _graph embedding_, which
usually refers to an embedding of a graph into the plane.

## Definition

```agda
module _
  {l1 l2 l3 l4 : Level} (G : Directed-Graph l1 l2) (H : Directed-Graph l3 l4)
  where

  is-emb-hom-Directed-Graph-Prop :
    hom-Directed-Graph G H → Prop (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  is-emb-hom-Directed-Graph-Prop f =
    product-Prop
      ( is-emb-Prop (vertex-hom-Directed-Graph G H f))
      ( Π-Prop
        ( vertex-Directed-Graph G)
        ( λ x →
          Π-Prop
            ( vertex-Directed-Graph G)
            ( λ y → is-emb-Prop (edge-hom-Directed-Graph G H f {x} {y}))))

  is-emb-hom-Directed-Graph : hom-Directed-Graph G H → UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  is-emb-hom-Directed-Graph f = type-Prop (is-emb-hom-Directed-Graph-Prop f)

  emb-Directed-Graph : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  emb-Directed-Graph = Σ (hom-Directed-Graph G H) is-emb-hom-Directed-Graph

  hom-emb-Directed-Graph : emb-Directed-Graph → hom-Directed-Graph G H
  hom-emb-Directed-Graph = pr1

  is-emb-emb-Directed-Graph :
    (f : emb-Directed-Graph) →
    is-emb-hom-Directed-Graph (hom-emb-Directed-Graph f)
  is-emb-emb-Directed-Graph = pr2
```

## External links

- [Graph homomorphism](https://www.wikidata.org/entity/Q3385162) on Wikidata
- [Graph homomorphism](https://en.wikipedia.org/wiki/Graph_homomorphism) on
  Wikipedia
