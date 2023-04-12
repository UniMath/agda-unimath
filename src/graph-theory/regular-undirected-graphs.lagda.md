# Regular undirected graph

```agda
module graph-theory.regular-undirected-graphs where
```

<details><summary>Imports</summary>

```agda
open import foundation.mere-equivalences
open import foundation.propositions
open import foundation.universe-levels

open import graph-theory.neighbors-undirected-graphs
open import graph-theory.undirected-graphs
```

</details>

## Idea

A regular undirected graph is a graph of which each vertex has the same number
of incident edges

## Definition

```agda
is-regular-undirected-graph-Prop :
  {l1 l2 l3 : Level} (X : UU l1)
  (G : Undirected-Graph l2 l3) → Prop (l1 ⊔ l2 ⊔ l3)
is-regular-undirected-graph-Prop X G =
  Π-Prop
    ( vertex-Undirected-Graph G)
    ( λ x → mere-equiv-Prop X (neighbor-Undirected-Graph G x))

is-regular-Undirected-Graph :
  {l1 l2 l3 : Level} (X : UU l1) (G : Undirected-Graph l2 l3) →
  UU (l1 ⊔ l2 ⊔ l3)
is-regular-Undirected-Graph X G =
  type-Prop (is-regular-undirected-graph-Prop X G)

is-prop-is-regular-Undirected-Graph :
  {l1 l2 l3 : Level} (X : UU l1) (G : Undirected-Graph l2 l3) →
  is-prop (is-regular-Undirected-Graph X G)
is-prop-is-regular-Undirected-Graph X G =
  is-prop-type-Prop (is-regular-undirected-graph-Prop X G)
```
