# Undirected graphs

```agda
module graph-theory.undirected-graphs where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.transport-along-identifications
open import foundation.universe-levels
open import foundation.unordered-pairs

open import graph-theory.directed-graphs
```

</details>

## Idea

An {{#concept "undirected graph" Agda=Undirected-Graph}} consists of a type `V`
of vertices and a family `E` of types over the
[unordered pairs](foundation.unordered-pairs.md) of `V`.

## Definition

```agda
Undirected-Graph : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
Undirected-Graph l1 l2 = Σ (UU l1) (λ V → unordered-pair V → UU l2)

module _
  {l1 l2 : Level} (G : Undirected-Graph l1 l2)
  where

  vertex-Undirected-Graph : UU l1
  vertex-Undirected-Graph = pr1 G

  unordered-pair-vertices-Undirected-Graph : UU (lsuc lzero ⊔ l1)
  unordered-pair-vertices-Undirected-Graph =
    unordered-pair vertex-Undirected-Graph

  type-unordered-pair-vertices-Undirected-Graph :
    unordered-pair-vertices-Undirected-Graph → UU lzero
  type-unordered-pair-vertices-Undirected-Graph p = type-unordered-pair p

  element-unordered-pair-vertices-Undirected-Graph :
    (p : unordered-pair-vertices-Undirected-Graph) →
    type-unordered-pair-vertices-Undirected-Graph p → vertex-Undirected-Graph
  element-unordered-pair-vertices-Undirected-Graph p = element-unordered-pair p

  edge-Undirected-Graph : unordered-pair-vertices-Undirected-Graph → UU l2
  edge-Undirected-Graph = pr2 G

  total-edge-Undirected-Graph : UU (lsuc lzero ⊔ l1 ⊔ l2)
  total-edge-Undirected-Graph =
    Σ unordered-pair-vertices-Undirected-Graph edge-Undirected-Graph
```

### The forgetful functor from directed graphs to undirected graphs

```agda
module _
  {l1 l2 : Level} (G : Directed-Graph l1 l2)
  where

  undirected-graph-Graph : Undirected-Graph l1 l2
  pr1 undirected-graph-Graph = vertex-Directed-Graph G
  pr2 undirected-graph-Graph p =
    Σ ( type-unordered-pair p)
      ( λ x →
        Σ ( type-unordered-pair p)
          ( λ y →
            edge-Directed-Graph G
              ( element-unordered-pair p x)
              ( element-unordered-pair p y)))

module _
  {l1 l2 : Level} (G : Undirected-Graph l1 l2)
  where

  graph-Undirected-Graph : Directed-Graph l1 (lsuc lzero ⊔ l1 ⊔ l2)
  pr1 graph-Undirected-Graph = vertex-Undirected-Graph G
  pr2 graph-Undirected-Graph x y =
    Σ ( unordered-pair-vertices-Undirected-Graph G)
      ( λ p →
        ( mere-Eq-unordered-pair (standard-unordered-pair x y) p) ×
        ( edge-Undirected-Graph G p))

  graph-Undirected-Graph' : Directed-Graph l1 l2
  pr1 graph-Undirected-Graph' = vertex-Undirected-Graph G
  pr2 graph-Undirected-Graph' x y =
    edge-Undirected-Graph G (standard-unordered-pair x y)
```

### Transporting edges along equalities of unordered pairs of vertices

```agda
module _
  {l1 l2 : Level} (G : Undirected-Graph l1 l2)
  where

  equiv-tr-edge-Undirected-Graph :
    (p q : unordered-pair-vertices-Undirected-Graph G)
    (α : Eq-unordered-pair p q) →
    edge-Undirected-Graph G p ≃ edge-Undirected-Graph G q
  equiv-tr-edge-Undirected-Graph p q α =
    equiv-tr (edge-Undirected-Graph G) (eq-Eq-unordered-pair' p q α)

  tr-edge-Undirected-Graph :
    (p q : unordered-pair-vertices-Undirected-Graph G)
    (α : Eq-unordered-pair p q) →
    edge-Undirected-Graph G p → edge-Undirected-Graph G q
  tr-edge-Undirected-Graph p q α =
    tr (edge-Undirected-Graph G) (eq-Eq-unordered-pair' p q α)
```

## External links

- [Graph](https://ncatlab.org/nlab/show/graph) at $n$Lab
- [Graph](https://www.wikidata.org/entity/Q141488) on Wikidata
- [Graph (discrete mathematics)](<https://en.wikipedia.org/wiki/Graph_(discrete_mathematics)>)
  at Wikipedia
- [Graph](https://mathworld.wolfram.com/Graph.html) at Wolfram MathWorld
