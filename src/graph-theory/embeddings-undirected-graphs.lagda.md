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

An embedding of undirected graphs is a morphism `f : G → H` of undirected graphs which is an embedding on vertices such that for each unordered pair `p` of vertices in `G` the map

```md
  edge-hom-Undirected-Graph G H :
    edge-Undirected-Graph G p →
    edge-Undirected-Graph H (unordered-pair-vertices-hom-Undirected-Graph G H f)
```

is also an embedding. Embeddings of undirected graphs correspond to undirected subgraphs.

## Definition

```agda
module _
  {l1 l2 l3 l4 : Level}
  (G : Undirected-Graph l1 l2) (H : Undirected-Graph l3 l4)
  where

  is-emb-hom-undirected-graph-Prop :
    hom-Undirected-Graph G H → Prop (lsuc lzero ⊔ l1 ⊔ l2 ⊔ l3 ⊔ l4)
  is-emb-hom-undirected-graph-Prop f =
    prod-Prop
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

- Faithful morphisms of undirected graphs
- Totally faithful morphisms of undirected graphs
