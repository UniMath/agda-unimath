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

A **finite undirected graph** consists of a
[finite set](univalent-combinatorics.finite-types.md) of vertices and a family
of finite types of edges indexed by
[unordered pairs](foundation.unordered-pairs.md) of vertices.

**Note:** In our definition of finite graph, we allow for the possibility that
there are multiple edges between the same two nodes. In discrete mathematics it
is also common to call such graphs _multigraphs_.

## Definitions

### Finite undirected graphs

```agda
Undirected-Graph-𝔽 : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
Undirected-Graph-𝔽 l1 l2 = Σ (𝔽 l1) (λ X → unordered-pair (type-𝔽 X) → 𝔽 l2)

module _
  {l1 l2 : Level} (G : Undirected-Graph-𝔽 l1 l2)
  where

  vertex-Undirected-Graph-𝔽 : UU l1
  vertex-Undirected-Graph-𝔽 = type-𝔽 (pr1 G)

  unordered-pair-vertices-Undirected-Graph-𝔽 : UU (lsuc lzero ⊔ l1)
  unordered-pair-vertices-Undirected-Graph-𝔽 =
    unordered-pair vertex-Undirected-Graph-𝔽

  is-finite-vertex-Undirected-Graph-𝔽 : is-finite vertex-Undirected-Graph-𝔽
  is-finite-vertex-Undirected-Graph-𝔽 = is-finite-type-𝔽 (pr1 G)

  edge-Undirected-Graph-𝔽 :
    (p : unordered-pair-vertices-Undirected-Graph-𝔽) → UU l2
  edge-Undirected-Graph-𝔽 p = type-𝔽 (pr2 G p)

  is-finite-edge-Undirected-Graph-𝔽 :
    (p : unordered-pair-vertices-Undirected-Graph-𝔽) →
    is-finite (edge-Undirected-Graph-𝔽 p)
  is-finite-edge-Undirected-Graph-𝔽 p = is-finite-type-𝔽 (pr2 G p)

  total-edge-Undirected-Graph-𝔽 : UU (lsuc lzero ⊔ l1 ⊔ l2)
  total-edge-Undirected-Graph-𝔽 =
    Σ unordered-pair-vertices-Undirected-Graph-𝔽 edge-Undirected-Graph-𝔽

  undirected-graph-Undirected-Graph-𝔽 : Undirected-Graph l1 l2
  pr1 undirected-graph-Undirected-Graph-𝔽 = vertex-Undirected-Graph-𝔽
  pr2 undirected-graph-Undirected-Graph-𝔽 = edge-Undirected-Graph-𝔽
```

### The following type is expected to be equivalent to Undirected-Graph-𝔽

```agda
Undirected-Graph-𝔽' : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
Undirected-Graph-𝔽' l1 l2 =
  Σ ( 𝔽 l1)
    ( λ V →
      Σ ( type-𝔽 V → type-𝔽 V → 𝔽 l2)
        ( λ E →
          Σ ( (x y : type-𝔽 V) → type-𝔽 (E x y) ≃ type-𝔽 (E y x))
            ( λ σ →
              (x y : type-𝔽 V) → map-equiv ((σ y x) ∘e (σ x y)) ~ id)))
```

The degree of a vertex x of a graph G is the set of occurences of x as an
endpoint of x. Note that the unordered pair {x,x} adds two elements to the
degree of x.

```agda
incident-edges-vertex-Undirected-Graph-𝔽 :
  {l1 l2 : Level} (G : Undirected-Graph-𝔽 l1 l2)
  (x : vertex-Undirected-Graph-𝔽 G) → UU (lsuc lzero ⊔ l1)
incident-edges-vertex-Undirected-Graph-𝔽 G x =
  Σ ( unordered-pair (vertex-Undirected-Graph-𝔽 G))
    ( λ p → fiber (element-unordered-pair p) x)
```

## External links

- [Multigraph](https://ncatlab.org/nlab/show/multigraph) at $n$Lab
- [Multigraph](https://www.wikidata.org/entity/Q2642629) on Wikidata
- [Multigraph](https://en.wikipedia.org/wiki/Multigraph) at Wikipedia
- [Multigraph](https://mathworld.wolfram.com/Multigraph.html) at Wolfram
  mathworld
