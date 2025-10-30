# Finite graphs

```agda
module graph-theory.finite-graphs where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.fibers-of-maps
open import foundation.function-types
open import foundation.homotopies
open import foundation.universe-levels
open import foundation.unordered-pairs

open import graph-theory.undirected-graphs

open import univalent-combinatorics.finite-types
```

</details>

## Idea

A {{#concept "finite undirected graph" Agda=Finite-Undirected-Graph}} consists
of a [finite set](univalent-combinatorics.finite-types.md) of vertices and a
family of finite types of edges indexed by
[unordered pairs](foundation.unordered-pairs.md) of vertices.

**Note:** In our definition of finite graph, we allow for the possibility that
there are multiple edges between the same two nodes. In discrete mathematics it
is also common to call such graphs _multigraphs_.

## Definitions

### Finite undirected graphs

```agda
Finite-Undirected-Graph : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
Finite-Undirected-Graph l1 l2 =
  Σ ( Finite-Type l1)
    ( λ X → unordered-pair (type-Finite-Type X) → Finite-Type l2)

module _
  {l1 l2 : Level} (G : Finite-Undirected-Graph l1 l2)
  where

  vertex-Finite-Undirected-Graph : UU l1
  vertex-Finite-Undirected-Graph = type-Finite-Type (pr1 G)

  unordered-pair-vertices-Finite-Undirected-Graph : UU (lsuc lzero ⊔ l1)
  unordered-pair-vertices-Finite-Undirected-Graph =
    unordered-pair vertex-Finite-Undirected-Graph

  is-finite-vertex-Finite-Undirected-Graph :
    is-finite vertex-Finite-Undirected-Graph
  is-finite-vertex-Finite-Undirected-Graph = is-finite-type-Finite-Type (pr1 G)

  edge-Finite-Undirected-Graph :
    (p : unordered-pair-vertices-Finite-Undirected-Graph) → UU l2
  edge-Finite-Undirected-Graph p = type-Finite-Type (pr2 G p)

  is-finite-edge-Finite-Undirected-Graph :
    (p : unordered-pair-vertices-Finite-Undirected-Graph) →
    is-finite (edge-Finite-Undirected-Graph p)
  is-finite-edge-Finite-Undirected-Graph p =
    is-finite-type-Finite-Type (pr2 G p)

  total-edge-Finite-Undirected-Graph : UU (lsuc lzero ⊔ l1 ⊔ l2)
  total-edge-Finite-Undirected-Graph =
    Σ unordered-pair-vertices-Finite-Undirected-Graph
      edge-Finite-Undirected-Graph

  undirected-graph-Finite-Undirected-Graph : Undirected-Graph l1 l2
  pr1 undirected-graph-Finite-Undirected-Graph = vertex-Finite-Undirected-Graph
  pr2 undirected-graph-Finite-Undirected-Graph = edge-Finite-Undirected-Graph
```

### The following type is expected to be equivalent to Finite-Undirected-Graph

```agda
Finite-Undirected-Graph' : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
Finite-Undirected-Graph' l1 l2 =
  Σ ( Finite-Type l1)
    ( λ V →
      Σ ( type-Finite-Type V → type-Finite-Type V → Finite-Type l2)
        ( λ E →
          Σ ( (x y : type-Finite-Type V) →
              type-Finite-Type (E x y) ≃ type-Finite-Type (E y x))
            ( λ σ →
              (x y : type-Finite-Type V) →
              map-equiv ((σ y x) ∘e (σ x y)) ~ id)))
```

The degree of a vertex x of a graph G is the set of occurrences of x as an
endpoint of x. Note that the unordered pair {x,x} adds two elements to the
degree of x.

```agda
incident-edges-vertex-Finite-Undirected-Graph :
  {l1 l2 : Level} (G : Finite-Undirected-Graph l1 l2)
  (x : vertex-Finite-Undirected-Graph G) → UU (lsuc lzero ⊔ l1)
incident-edges-vertex-Finite-Undirected-Graph G x =
  Σ ( unordered-pair (vertex-Finite-Undirected-Graph G))
    ( λ p → fiber (element-unordered-pair p) x)
```

## External links

- [Multigraph](https://ncatlab.org/nlab/show/multigraph) at $n$Lab
- [Multigraph](https://www.wikidata.org/entity/Q2642629) on Wikidata
- [Multigraph](https://en.wikipedia.org/wiki/Multigraph) at Wikipedia
- [Multigraph](https://mathworld.wolfram.com/Multigraph.html) at Wolfram
  mathworld
