---
title: Enriched directed trees
---

```
module trees.enriched-directed-trees where

open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.universe-levels

open import graph-theory.directed-graphs

open import trees.directed-trees
```

## Idea

Consider a type `A` and a type family `B` over `A`. An `(A,B)`-enriched directed tree is a directed tree `T` equipped with a map

```md
  shape : node-Directed-Tree T → A
```

and for each node `x` an equivalence

```md
  e : B (shape x) ≃ Σ (node-Directed-Tree T) (λ y → edge-Directed-Tree T y x)
```

By this equivalence, there is a higher group action of `Ω (A , f x)` on the type of children of `x`. We show that the type of `(A , B)`-enriched directed trees is equivalent to the type `𝕎 A B`.

## Definition

```agda
module _
  {l1 l2 : Level} (l3 l4 : Level) (A : UU l1) (B : A → UU l2)
  where
  
  Enriched-Directed-Tree : UU (l1 ⊔ l2 ⊔ lsuc l3 ⊔ lsuc l4)
  Enriched-Directed-Tree =
    Σ ( Directed-Tree l3 l4)
      ( λ T →
        Σ ( node-Directed-Tree T → A)
          ( λ f →
            (x : node-Directed-Tree T) →
            B (f x) ≃
            Σ (node-Directed-Tree T) (λ y → edge-Directed-Tree T y x)))

  module _
    (T : Enriched-Directed-Tree)
    where

    directed-tree-Enriched-Directed-Tree : Directed-Tree l3 l4
    directed-tree-Enriched-Directed-Tree = pr1 T

    graph-Enriched-Directed-Tree : Directed-Graph l3 l4
    graph-Enriched-Directed-Tree =
      graph-Directed-Tree directed-tree-Enriched-Directed-Tree

    node-Enriched-Directed-Tree : UU l3
    node-Enriched-Directed-Tree =
      node-Directed-Tree directed-tree-Enriched-Directed-Tree

    edge-Enriched-Directed-Tree :
      (x y : node-Enriched-Directed-Tree) → UU l4
    edge-Enriched-Directed-Tree =
      edge-Directed-Tree directed-tree-Enriched-Directed-Tree

    root-Enriched-Directed-Tree : node-Enriched-Directed-Tree
    root-Enriched-Directed-Tree =
      root-Directed-Tree directed-tree-Enriched-Directed-Tree

    is-tree-Enriched-Directed-Tree :
      is-tree-Directed-Graph
        graph-Enriched-Directed-Tree
        root-Enriched-Directed-Tree
    is-tree-Enriched-Directed-Tree =
      is-tree-Directed-Tree directed-tree-Enriched-Directed-Tree

    shape-Enriched-Directed-Tree : node-Enriched-Directed-Tree → A
    shape-Enriched-Directed-Tree = pr1 (pr2 T)

    equiv-children-Enriched-Directed-Tree :
      (x : node-Enriched-Directed-Tree) →
      B (shape-Enriched-Directed-Tree x) ≃
      Σ (node-Enriched-Directed-Tree) (λ y → edge-Enriched-Directed-Tree y x)
    equiv-children-Enriched-Directed-Tree = pr2 (pr2 T)
```
