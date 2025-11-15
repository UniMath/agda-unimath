# Wide displayed large reflexive graphs

```agda
module graph-theory.wide-displayed-large-reflexive-graphs where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.unit-type
open import foundation.universe-levels

open import graph-theory.large-reflexive-graphs
open import graph-theory.reflexive-graphs
```

</details>

## Idea

A
{{#concept "wide displayed large reflexive graph" Agda=Wide-Displayed-Large-Reflexive-Graph}}
is a
[displayed large reflexive graph](graph-theory.displayed-large-reflexive-graphs.md)
over a base [large reflexive graph](graph-theory.large-reflexive-graphs.md) `G`
that only adds structure on the edges.

**Terminology.** The use of the term "wide" here is motivated by the idea that a
"wide displayed graph" should generalize "wide subgraphs", i.e., a subgraph
which contains all vertices, in the same way "displayed graphs" generalize
"subgraphs".

## Definitions

### Wide displayed large reflexive graphs

```agda
record
  Wide-Displayed-Large-Reflexive-Graph
  {α' : Level → Level} {β' : Level → Level → Level}
  (β : Level → Level → Level)
  (G : Large-Reflexive-Graph α' β') : UUω
  where

  field

    edge-Wide-Displayed-Large-Reflexive-Graph :
      {l1 l2 : Level}
      {x : vertex-Large-Reflexive-Graph G l1}
      {y : vertex-Large-Reflexive-Graph G l2}
      (f : edge-Large-Reflexive-Graph G x y) →
      UU (β l1 l2)

    refl-Wide-Displayed-Large-Reflexive-Graph :
      {l : Level}
      (x : vertex-Large-Reflexive-Graph G l) →
      edge-Wide-Displayed-Large-Reflexive-Graph (refl-Large-Reflexive-Graph G x)

open Wide-Displayed-Large-Reflexive-Graph public
```

### The total large reflexive graph of a displayed large reflexive graph

```agda
module _
  {α1 : Level → Level} {β1 β2 : Level → Level → Level}
  {G : Large-Reflexive-Graph α1 β1}
  (H : Wide-Displayed-Large-Reflexive-Graph β2 G)
  where

  vertex-total-large-reflexive-graph-Wide-Displayed-Large-Reflexive-Graph :
    (l : Level) → UU (α1 l)
  vertex-total-large-reflexive-graph-Wide-Displayed-Large-Reflexive-Graph l =
    vertex-Large-Reflexive-Graph G l

  edge-total-large-reflexive-graph-Wide-Displayed-Large-Reflexive-Graph :
    {l1 l2 : Level} →
    vertex-total-large-reflexive-graph-Wide-Displayed-Large-Reflexive-Graph l1 →
    vertex-total-large-reflexive-graph-Wide-Displayed-Large-Reflexive-Graph l2 →
    UU (β1 l1 l2 ⊔ β2 l1 l2)
  edge-total-large-reflexive-graph-Wide-Displayed-Large-Reflexive-Graph x y =
    Σ ( edge-Large-Reflexive-Graph G x y)
      ( edge-Wide-Displayed-Large-Reflexive-Graph H)

  refl-total-large-reflexive-graph-Wide-Displayed-Large-Reflexive-Graph :
    {l : Level}
    (x :
      vertex-total-large-reflexive-graph-Wide-Displayed-Large-Reflexive-Graph
        l) →
    edge-total-large-reflexive-graph-Wide-Displayed-Large-Reflexive-Graph x x
  refl-total-large-reflexive-graph-Wide-Displayed-Large-Reflexive-Graph x =
    ( refl-Large-Reflexive-Graph G x ,
      refl-Wide-Displayed-Large-Reflexive-Graph H x)

  total-large-reflexive-graph-Wide-Displayed-Large-Reflexive-Graph :
    Large-Reflexive-Graph α1 (λ l1 l2 → β1 l1 l2 ⊔ β2 l1 l2)
  vertex-Large-Reflexive-Graph
    total-large-reflexive-graph-Wide-Displayed-Large-Reflexive-Graph =
      vertex-total-large-reflexive-graph-Wide-Displayed-Large-Reflexive-Graph
  edge-Large-Reflexive-Graph
    total-large-reflexive-graph-Wide-Displayed-Large-Reflexive-Graph =
    edge-total-large-reflexive-graph-Wide-Displayed-Large-Reflexive-Graph
  refl-Large-Reflexive-Graph
    total-large-reflexive-graph-Wide-Displayed-Large-Reflexive-Graph =
    refl-total-large-reflexive-graph-Wide-Displayed-Large-Reflexive-Graph
```

### The fiber reflexive graph of a wide displayed large reflexive graph over a vertex

```agda
module _
  {α1 : Level → Level} {β1 β2 : Level → Level → Level}
  {G : Large-Reflexive-Graph α1 β1}
  (H : Wide-Displayed-Large-Reflexive-Graph β2 G)
  {l : Level} (x : vertex-Large-Reflexive-Graph G l)
  where

  fiber-vertex-reflexive-graph-Wide-Displayed-Large-Reflexive-Graph :
    Reflexive-Graph lzero (β2 l l)
  pr1 (pr1 fiber-vertex-reflexive-graph-Wide-Displayed-Large-Reflexive-Graph) =
    unit
  pr2 (pr1 fiber-vertex-reflexive-graph-Wide-Displayed-Large-Reflexive-Graph)
    _ _ =
    edge-Wide-Displayed-Large-Reflexive-Graph H (refl-Large-Reflexive-Graph G x)
  pr2 fiber-vertex-reflexive-graph-Wide-Displayed-Large-Reflexive-Graph _ =
    refl-Wide-Displayed-Large-Reflexive-Graph H x
```
