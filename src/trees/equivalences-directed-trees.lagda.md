# Equivalences of directed trees

```agda
module trees.equivalences-directed-trees where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-transport
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.functions
open import foundation.homotopies
open import foundation.identity-types
open import foundation.universe-levels

open import graph-theory.equivalences-directed-graphs
open import graph-theory.walks-directed-graphs

open import trees.directed-trees
```

</details>

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

  inv-node-equiv-Directed-Tree :
    node-Directed-Tree T → node-Directed-Tree S
  inv-node-equiv-Directed-Tree =
    inv-vertex-equiv-Directed-Graph
      ( graph-Directed-Tree S)
      ( graph-Directed-Tree T)
      ( e)

  issec-inv-node-equiv-Directed-Tree :
    ( node-equiv-Directed-Tree ∘ inv-node-equiv-Directed-Tree) ~ id
  issec-inv-node-equiv-Directed-Tree =
    issec-inv-vertex-equiv-Directed-Graph
      ( graph-Directed-Tree S)
      ( graph-Directed-Tree T)
      ( e)

  isretr-inv-node-equiv-Directed-Tree :
    ( inv-node-equiv-Directed-Tree ∘ node-equiv-Directed-Tree) ~ id
  isretr-inv-node-equiv-Directed-Tree =
    isretr-inv-vertex-equiv-Directed-Graph
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

## Properties

### Equivalences of directed trees preserve the root

```agda
module _
  {l1 l2 l3 l4 : Level} (S : Directed-Tree l1 l2) (T : Directed-Tree l3 l4)
  (e : equiv-Directed-Tree S T)
  where

  preserves-root-equiv-Directed-Tree :
    node-equiv-Directed-Tree S T e (root-Directed-Tree S) ＝
    root-Directed-Tree T
  preserves-root-equiv-Directed-Tree =
    inv
      ( uniqueness-root-Directed-Tree T
        ( pair
          ( node-equiv-Directed-Tree S T e (root-Directed-Tree S))
          ( λ y →
            is-contr-equiv'
              ( walk-Directed-Tree S
                ( inv-node-equiv-Directed-Tree S T e y)
                ( root-Directed-Tree S))
              ( ( equiv-binary-tr
                  ( walk-Directed-Graph (graph-Directed-Tree T))
                  ( issec-inv-node-equiv-Directed-Tree S T e y)
                  ( refl)) ∘e
                ( equiv-walk-equiv-Directed-Graph
                  ( graph-Directed-Tree S)
                  ( graph-Directed-Tree T)
                  ( e)))
              ( is-tree-Directed-Tree' S
                ( inv-node-equiv-Directed-Tree S T e y)))))
```
