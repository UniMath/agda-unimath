# Vertex covers

```agda
open import foundation.function-extensionality-axiom

module
  graph-theory.vertex-covers
  (funext : function-extensionality)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types funext
open import foundation.coproduct-types funext
open import foundation.dependent-pair-types
open import foundation.identity-types funext
open import foundation.propositional-truncations funext
open import foundation.unit-type
open import foundation.universe-levels
open import foundation.unordered-pairs funext

open import graph-theory.undirected-graphs funext

open import univalent-combinatorics.standard-finite-types funext
```

</details>

## Idea

A **vertex cover** on a [undirect graph](graph-theory.undirected-graphs.md) is a
set of vertices that includes at least one extremity of each edge of the graph.

## Definitions

```agda
vertex-cover :
  {l1 l2 : Level} → Undirected-Graph l1 l2 → UU (lsuc lzero ⊔ l1 ⊔ l2)
vertex-cover G =
  Σ ( vertex-Undirected-Graph G → Fin 2)
    ( λ c →
      (p : unordered-pair-vertices-Undirected-Graph G) →
      edge-Undirected-Graph G p →
        type-trunc-Prop
          ( Σ (vertex-Undirected-Graph G)
            ( λ x → is-in-unordered-pair p x × Id (c x) (inr star))))
```

## External links

- [Vertex cover](https://en.wikipedia.org/wiki/Vertex_cover) at Wikipedia
- [Vertex cover](https://mathworld.wolfram.com/VertexCover.html) at Wolfram
  MathWorld
- [Vertex cover problem](https://www.wikidata.org/entity/Q924362) on Wikidata
