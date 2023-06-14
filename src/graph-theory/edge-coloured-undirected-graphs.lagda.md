# Edge-coloured undirected graphs

```agda
module graph-theory.edge-coloured-undirected-graphs where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.universe-levels
open import foundation.unordered-pairs

open import graph-theory.neighbors-undirected-graphs
open import graph-theory.undirected-graphs
```

</details>

## Idea

An edge-coloured undirected graph is an undirected graph equipped with a family
of maps `E p → X` from the edges at unordered pairs `p` into a type `C` of
colours, such that the induced map `incident-Undirected-Graph G x → C` is
injective for each vertex `x`.

## Definition

```agda
module _
  {l1 l2 l3 : Level} (C : UU l1) (G : Undirected-Graph l2 l3)
  where

  neighbor-edge-colouring-Undirected-Graph :
    ( (p : unordered-pair-vertices-Undirected-Graph G) →
      edge-Undirected-Graph G p → C) →
    (x : vertex-Undirected-Graph G) → neighbor-Undirected-Graph G x → C
  neighbor-edge-colouring-Undirected-Graph f x (pair y e) =
    f (standard-unordered-pair x y) e

  edge-colouring-Undirected-Graph : UU (lsuc lzero ⊔ l1 ⊔ l2 ⊔ l3)
  edge-colouring-Undirected-Graph =
    Σ ( (p : unordered-pair-vertices-Undirected-Graph G) →
        edge-Undirected-Graph G p → C)
      ( λ f →
        (x : vertex-Undirected-Graph G) →
        is-emb (neighbor-edge-colouring-Undirected-Graph f x))

Edge-Coloured-Undirected-Graph :
  {l : Level} (l1 l2 : Level) (C : UU l) → UU (l ⊔ lsuc l1 ⊔ lsuc l2)
Edge-Coloured-Undirected-Graph l1 l2 C =
  Σ ( Undirected-Graph l1 l2)
    ( edge-colouring-Undirected-Graph C)

module _
  {l1 l2 l3 : Level} {C : UU l1} (G : Edge-Coloured-Undirected-Graph l2 l3 C)
  where

  undirected-graph-Edge-Coloured-Undirected-Graph : Undirected-Graph l2 l3
  undirected-graph-Edge-Coloured-Undirected-Graph = pr1 G

  vertex-Edge-Coloured-Undirected-Graph : UU l2
  vertex-Edge-Coloured-Undirected-Graph =
    vertex-Undirected-Graph undirected-graph-Edge-Coloured-Undirected-Graph

  unordered-pair-vertices-Edge-Coloured-Undirected-Graph : UU (lsuc lzero ⊔ l2)
  unordered-pair-vertices-Edge-Coloured-Undirected-Graph =
    unordered-pair-vertices-Undirected-Graph
      undirected-graph-Edge-Coloured-Undirected-Graph

  edge-Edge-Coloured-Undirected-Graph :
    unordered-pair-vertices-Edge-Coloured-Undirected-Graph → UU l3
  edge-Edge-Coloured-Undirected-Graph =
    edge-Undirected-Graph undirected-graph-Edge-Coloured-Undirected-Graph

  neighbor-Edge-Coloured-Undirected-Graph :
    vertex-Edge-Coloured-Undirected-Graph → UU (l2 ⊔ l3)
  neighbor-Edge-Coloured-Undirected-Graph =
    neighbor-Undirected-Graph undirected-graph-Edge-Coloured-Undirected-Graph

  colouring-Edge-Coloured-Undirected-Graph :
    (p : unordered-pair-vertices-Edge-Coloured-Undirected-Graph) →
    edge-Edge-Coloured-Undirected-Graph p → C
  colouring-Edge-Coloured-Undirected-Graph =
    pr1 (pr2 G)

  neighbor-colouring-Edge-Coloured-Undirected-Graph :
    (x : vertex-Edge-Coloured-Undirected-Graph) →
    neighbor-Edge-Coloured-Undirected-Graph x → C
  neighbor-colouring-Edge-Coloured-Undirected-Graph =
    neighbor-edge-colouring-Undirected-Graph C
      undirected-graph-Edge-Coloured-Undirected-Graph
      colouring-Edge-Coloured-Undirected-Graph

  is-emb-colouring-Edge-Coloured-Undirected-Graph :
    (x : vertex-Edge-Coloured-Undirected-Graph) →
    is-emb (neighbor-colouring-Edge-Coloured-Undirected-Graph x)
  is-emb-colouring-Edge-Coloured-Undirected-Graph =
    pr2 (pr2 G)
```
