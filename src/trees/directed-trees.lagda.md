---
title: Directed trees
---

```agda
module trees.directed-trees where

open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.propositions
open import foundation.universe-levels

open import graph-theory.directed-graphs
open import graph-theory.trails-directed-graphs
```

## Idea

A directed tree is a directed graph `G` equipped with a rood `r : G` such that for every vertex `x : G` the type of trails from `x` to `r` is contractible.

## Definition

```agda
is-directed-tree-Graph-Prop :
  {l1 l2 : Level} (G : Graph l1 l2) (r : vertex-Graph G) → Prop (l1 ⊔ l2)
is-directed-tree-Graph-Prop G r =
  Π-Prop
    ( vertex-Graph G)
    ( λ x → is-contr-Prop (trail-Graph G x r))

is-directed-tree-Graph :
  {l1 l2 : Level} (G : Graph l1 l2) (r : vertex-Graph G) → UU (l1 ⊔ l2)
is-directed-tree-Graph G r = type-Prop (is-directed-tree-Graph-Prop G r)

Directed-Tree : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
Directed-Tree l1 l2 =
  Σ ( Graph l1 l2)
    ( λ G →
      Σ ( vertex-Graph G)
        ( λ r → is-directed-tree-Graph G r))
```
