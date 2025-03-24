# Regular undirected graph

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module graph-theory.regular-undirected-graphs
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-products-propositions funext
open import foundation.mere-equivalences funext univalence truncations
open import foundation.propositions funext univalence
open import foundation.universe-levels

open import graph-theory.neighbors-undirected-graphs funext univalence truncations
open import graph-theory.undirected-graphs funext univalence truncations
```

</details>

## Idea

A **regular undirected graph** is an
[undirected graph](graph-theory.undirected-graphs.md) of which each vertex has
the same number of
[incident edges](graph-theory.neighbors-undirected-graphs.md).

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

## External links

- [Regular graph](https://d3gt.com/unit.html?regular-graph) at D3 Graph Theory
- [Regular graph](https://www.wikidata.org/entity/Q826467) on Wikidata
- [Regular graph](https://en.wikipedia.org/wiki/Regular_graph) at Wikipedia
- [Regular graph](https://mathworld.wolfram.com/RegularGraph.html) at Wolfram
  MathWorld
