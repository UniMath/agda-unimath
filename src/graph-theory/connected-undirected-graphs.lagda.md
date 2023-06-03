# Connected graphs

```agda
module graph-theory.connected-undirected-graphs where
```

<details><summary>Imports</summary>

```agda
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.universe-levels

open import graph-theory.undirected-graphs
open import graph-theory.walks-undirected-graphs
```

</details>

## Idea

A graph is said to be connected if any point can be reached from any point by a
walk.

## Definition

```agda
module _
  {l1 l2 : Level} (G : Undirected-Graph l1 l2)
  where

  is-connected-Undirected-Graph : UU (l1 ⊔ l2 ⊔ lsuc lzero)
  is-connected-Undirected-Graph =
    (x y : vertex-Undirected-Graph G) →
    type-trunc-Prop (walk-Undirected-Graph G x y)
```

## Properties

### The property of being connected for an undirected graph is a proposition

```agda
  is-prop-is-connected-Undirected-Graph
    : is-prop is-connected-Undirected-Graph
  is-prop-is-connected-Undirected-Graph =
    is-prop-Π (λ _ → is-prop-Π (λ _ → is-prop-type-trunc-Prop))
```
