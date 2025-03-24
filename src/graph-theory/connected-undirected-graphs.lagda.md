# Connected graphs

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module graph-theory.connected-undirected-graphs
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-products-propositions funext
open import foundation.propositional-truncations funext univalence
open import foundation.propositions funext univalence
open import foundation.universe-levels

open import graph-theory.undirected-graphs funext univalence truncations
open import graph-theory.walks-undirected-graphs funext univalence truncations
```

</details>

## Idea

An [undirected graph](graph-theory.undirected-graphs.md) is said to be
**connected** if any point can be reached from any point by a
[walk](graph-theory.walks-undirected-graphs.md).

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

## External links

- [Connected graph](https://ncatlab.org/nlab/show/connected+graph) at $n$Lab
- [Connected graph](https://www.wikidata.org/entity/Q230655) on Wikidata
- [Connectivity (graph theory)](<https://en.wikipedia.org/wiki/Connectivity_(graph_theory)>)
  on Wikipedia
- [Connected graph](https://mathworld.wolfram.com/ConnectedGraph.html) at
  Wolfram MathWorld
