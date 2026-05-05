# Hydrocarbons

```agda
module organic-chemistry.hydrocarbons where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.inequality-natural-numbers

open import finite-group-theory.tetrahedra-in-3-space

open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.negation
open import foundation.universe-levels
open import foundation.unordered-pairs

open import graph-theory.connected-undirected-graphs
open import graph-theory.finite-graphs

open import univalent-combinatorics.finite-types
```

</details>

## Idea

We define the type of all theoretically possible hydrocarbons, correctly
accounting for the symmetries between hydrocarbons and the different isomers.

Hydrocarbons are built out of carbon and hydrogen atoms. The symmetry group of
an isolated carbon atom in 3-space is the alternating group `A₄`, where the
number 4 comes from the number of bonds a carbon atom makes in a molecule.

Bonds in hydrocarbons can appear as single bonds, double bonds, and triple
bonds, but there are no quadruple bonds.

We define
{{#concept "hydrocarbons" WD="hydrocarbon" WDID=Q43648 Agda=hydrocarbon}} to be
[graphs](graph-theory.finite-graphs.md) equipped with a family of
[tetrahedra in 3-dimensional space](finite-group-theory.tetrahedra-in-3-space.md)
indexed by the vertices and for each vertex `c` an
[embedding](foundation-core.embeddings.md) from the type of all edges incident
to `c` into the vertices of the tetrahedron associated to `c`, satisfying the
following conditions:

- There are at most 3 edges between any two vertices
- The graph contains no loops
- The graph is connected

## Definition

```agda
hydrocarbon : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
hydrocarbon l1 l2 =
  Σ ( Finite-Undirected-Graph l1 l2)
    ( λ G →
      Σ ( vertex-Finite-Undirected-Graph G → tetrahedron-in-3-space)
        ( λ C →
          ( ( c : vertex-Finite-Undirected-Graph G) →
            Σ ( vertex-Finite-Undirected-Graph G)
              ( λ c' →
                edge-Finite-Undirected-Graph G (standard-unordered-pair c c')) ↪
                type-Type-With-Cardinality-ℕ 4 (pr1 (C c))) ×
          ( ( (c : vertex-Finite-Undirected-Graph G) →
              ¬ ( edge-Finite-Undirected-Graph G
                  ( standard-unordered-pair c c))) ×
            ( ( (c c' : vertex-Finite-Undirected-Graph G) →
                leq-ℕ
                  ( number-of-elements-is-finite
                    ( is-finite-type-Finite-Type
                      ( pr2 G (standard-unordered-pair c c'))))
                  ( 3)) ×
              ( is-connected-Undirected-Graph
                ( undirected-graph-Finite-Undirected-Graph G))))))

module _
  {l1 l2 : Level} (H : hydrocarbon l1 l2)
  where

  finite-graph-hydrocarbon : Finite-Undirected-Graph l1 l2
  finite-graph-hydrocarbon = pr1 H

  vertex-hydrocarbon-Finite-Type : Finite-Type l1
  vertex-hydrocarbon-Finite-Type = pr1 finite-graph-hydrocarbon

  vertex-hydrocarbon : UU l1
  vertex-hydrocarbon = vertex-Finite-Undirected-Graph finite-graph-hydrocarbon

  is-finite-vertex-hydrocarbon : is-finite vertex-hydrocarbon
  is-finite-vertex-hydrocarbon =
    is-finite-vertex-Finite-Undirected-Graph finite-graph-hydrocarbon

  unordered-pair-vertices-hydrocarbon : UU (lsuc lzero ⊔ l1)
  unordered-pair-vertices-hydrocarbon = unordered-pair vertex-hydrocarbon

  edge-hydrocarbon-Finite-Type :
    unordered-pair-vertices-hydrocarbon → Finite-Type l2
  edge-hydrocarbon-Finite-Type = pr2 finite-graph-hydrocarbon

  edge-hydrocarbon : unordered-pair-vertices-hydrocarbon → UU l2
  edge-hydrocarbon = edge-Finite-Undirected-Graph finite-graph-hydrocarbon

  is-finite-edge-hydrocarbon :
    (p : unordered-pair-vertices-hydrocarbon) → is-finite (edge-hydrocarbon p)
  is-finite-edge-hydrocarbon =
    is-finite-edge-Finite-Undirected-Graph finite-graph-hydrocarbon

  carbon-atom-hydrocarbon :
    vertex-hydrocarbon → tetrahedron-in-3-space
  carbon-atom-hydrocarbon = pr1 (pr2 H)

  electron-carbon-atom-hydrocarbon :
    (c : vertex-hydrocarbon) → UU lzero
  electron-carbon-atom-hydrocarbon c =
    vertex-tetrahedron-in-3-space (carbon-atom-hydrocarbon c)

  emb-bonding-hydrocarbon :
    (c : vertex-hydrocarbon) →
    Σ vertex-hydrocarbon
      ( λ c' → edge-hydrocarbon (standard-unordered-pair c c')) ↪
    electron-carbon-atom-hydrocarbon c
  emb-bonding-hydrocarbon = pr1 (pr2 (pr2 H))

  bonding-hydrocarbon :
    {c c' : vertex-hydrocarbon} →
    edge-hydrocarbon (standard-unordered-pair c c') →
    electron-carbon-atom-hydrocarbon c
  bonding-hydrocarbon {c} {c'} b =
    map-emb (emb-bonding-hydrocarbon c) (c' , b)
```
