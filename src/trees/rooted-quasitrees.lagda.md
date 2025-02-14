# Rooted quasitrees

```agda
module trees.rooted-quasitrees where
```

<details><summary>Imports</summary>

```agda
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import graph-theory.trails-undirected-graphs
open import graph-theory.undirected-graphs
```

</details>

## Idea

A **rooted quasitree** is an undirected graph `G` equipped with a marked
vertex`r`, to be called the root, such that for every vertex `x` there is a
unique trail from `r` to `x`.

## Definition

```agda
is-rooted-quasitree-Undirected-Graph :
  {l1 l2 : Level} (G : Undirected-Graph l1 l2) →
  vertex-Undirected-Graph G → UU (lone ⊔ l1 ⊔ l2)
is-rooted-quasitree-Undirected-Graph G r =
  (x : vertex-Undirected-Graph G) → is-contr (trail-Undirected-Graph G r x)

Rooted-Quasitree : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
Rooted-Quasitree l1 l2 =
  Σ ( Undirected-Graph l1 l2)
    ( λ G →
      Σ ( vertex-Undirected-Graph G)
        ( is-rooted-quasitree-Undirected-Graph G))
```
