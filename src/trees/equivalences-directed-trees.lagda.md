---
title: Equivalences of directed trees
---

```agda
module trees.equivalences-directed-trees where

open import foundation.equivalences
open import foundation.universe-levels

open import graph-theory.equivalences-directed-graphs

open import trees.directed-trees
```

## Definition

```agda
equiv-Directed-Tree :
  {l1 l2 l3 l4 : Level} (S : Directed-Tree l1 l2) (T : Directed-Tree l3 l4) →
  UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
equiv-Directed-Tree S T =
  equiv-Directed-Graph (graph-Directed-Tree S) (graph-Directed-Tree T)

module _
  {l1 l2 l3 l4 : Level} (S : Directed-Tree l1 l2) (T : Directed-Tree l3 l4)
  (e : equiv-Directed-Tree S T)
  where

  equiv-node-equiv-Directed-Tree :
    node-Directed-Tree S ≃ node-Directed-Tree T
  equiv-node-equiv-Directed-Tree =
    equiv-vertex-equiv-Directed-Graph
      ( graph-Directed-Tree S)
      ( graph-Directed-Tree T)
      ( e)

  node-equiv-Directed-Tree :
    node-Directed-Tree S → node-Directed-Tree T
  node-equiv-Directed-Tree =
    vertex-equiv-Directed-Graph
      ( graph-Directed-Tree S)
      ( graph-Directed-Tree T)
      ( e)

  equiv-edge-equiv-Directed-Tree :
    (x y : node-Directed-Tree S) →
    edge-Directed-Tree S x y ≃
    edge-Directed-Tree T
      ( node-equiv-Directed-Tree x)
      ( node-equiv-Directed-Tree y)
  equiv-edge-equiv-Directed-Tree =
    equiv-edge-equiv-Directed-Graph
      ( graph-Directed-Tree S)
      ( graph-Directed-Tree T)
      ( e)

  edge-equiv-Directed-Tree :
    (x y : node-Directed-Tree S) →
    edge-Directed-Tree S x y →
    edge-Directed-Tree T
      ( node-equiv-Directed-Tree x)
      ( node-equiv-Directed-Tree y)
  edge-equiv-Directed-Tree =
    edge-equiv-Directed-Graph
      ( graph-Directed-Tree S)
      ( graph-Directed-Tree T)
      ( e)
```
