---
title: Embeddings of directed graphs
---

```
module graph-theory.embeddings-directed-graphs where

open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.propositions
open import foundation.universe-levels

open import graph-theory.directed-graphs
open import graph-theory.morphisms-directed-graphs
```

## Idea

An embedding of directed graphs is a morphism `f : G → H` of directed graphs which is an embedding on vertices such that for each pair `(x , y)` of vertices in `G` the map

```md
  edge-hom-Graph G H : edge-Graph G p → edge-Graph H x y
```

is also an embedding. Embeddings of directed graphs correspond to directed subgraphs.

## Definition

```agda
module _
  {l1 l2 l3 l4 : Level} (G : Graph l1 l2) (H : Graph l3 l4)
  where

  is-emb-hom-Graph-Prop : hom-Graph G H → Prop (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  is-emb-hom-Graph-Prop f =
    prod-Prop
      ( is-emb-Prop (vertex-hom-Graph G H f))
      ( Π-Prop
        ( vertex-Graph G)
        ( λ x →
          Π-Prop
            ( vertex-Graph G)
            ( λ y → is-emb-Prop (edge-hom-Graph G H f {x} {y}))))

  is-emb-hom-Graph : hom-Graph G H → UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  is-emb-hom-Graph f = type-Prop (is-emb-hom-Graph-Prop f)

  emb-Graph : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  emb-Graph = Σ (hom-Graph G H) is-emb-hom-Graph

  hom-emb-Graph : emb-Graph → hom-Graph G H
  hom-emb-Graph = pr1

  is-emb-emb-Graph : (f : emb-Graph) → is-emb-hom-Graph (hom-emb-Graph f)
  is-emb-emb-Graph = pr2
```

