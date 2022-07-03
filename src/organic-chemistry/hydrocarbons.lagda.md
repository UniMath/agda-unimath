---
title: Hydrocarbons
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module organic-chemistry.hydrocarbons where

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

## Idea

We define the type of all theoretically possible hydrocarbons, correctly accounting for the symmetries between hydrocarbons and the different isomers.

Hydrocarbons are built out of carbon and hydrogen atoms. The symmetry group of an isolated carbon atom in 3-space is the alternating group `A₄`, where the number 4 comes from the number of bonds a carbon atom makes in a molecule.

Bonds in hydrocarbons can appear as single bonds, double bonds, and triple bonds, but there are no quadruple bonds.

We define hydrocarbons to be graphs equipped with a family of tetrahedra in 3-dimensional space indexed by the vertices and for each vertex `c` an embedding from the type of all edges incident to `c` into the vertices of the tetrahedron associated to `c`, satisfying the following conditions:

- There are at most 3 edges between any two vertices
- The graph contains no loops
- The graph is connected

## Definition

```agda
hydrocarbon : UU (lsuc lzero)
hydrocarbon =
  Σ ( Undirected-Graph-𝔽)
    ( λ G →
      Σ ( vertex-Undirected-Graph-𝔽 G → tetrahedron-in-3-space)
        ( λ C →
          ( ( c : vertex-Undirected-Graph-𝔽 G) →
            Σ ( vertex-Undirected-Graph-𝔽 G)
              ( λ c' →
                edge-Undirected-Graph-𝔽 G (standard-unordered-pair c c')) ↪
                type-UU-Fin (pr1 (C c))) ×
          ( ( (c : vertex-Undirected-Graph-𝔽 G) →
              ¬ ( edge-Undirected-Graph-𝔽 G
                  ( standard-unordered-pair c c))) ×
            ( ( (c c' : vertex-Undirected-Graph-𝔽 G) →
                leq-ℕ
                  ( number-of-elements-is-finite
                    ( is-finite-type-𝔽 (pr2 G (standard-unordered-pair c c'))))
                  ( 3)) ×
                is-connected-Undirected-Graph
                  ( undirected-graph-Undirected-Graph-𝔽 G)))))

module _
  (H : hydrocarbon)
  where

  finite-graph-hydrocarbon : Undirected-Graph-𝔽
  finite-graph-hydrocarbon = pr1 H

  vertex-hydrocarbon-𝔽 : 𝔽
  vertex-hydrocarbon-𝔽 = pr1 finite-graph-hydrocarbon

  vertex-hydrocarbon : UU lzero
  vertex-hydrocarbon = vertex-Undirected-Graph-𝔽 finite-graph-hydrocarbon

  is-finite-vertex-hydrocarbon : is-finite vertex-hydrocarbon
  is-finite-vertex-hydrocarbon =
    is-finite-vertex-Undirected-Graph-𝔽 finite-graph-hydrocarbon

  unordered-pair-vertices-hydrocarbon : UU (lsuc lzero)
  unordered-pair-vertices-hydrocarbon = unordered-pair vertex-hydrocarbon

  edge-hydrocarbon-𝔽 : unordered-pair-vertices-hydrocarbon → 𝔽
  edge-hydrocarbon-𝔽 = pr2  finite-graph-hydrocarbon

  edge-hydrocarbon : unordered-pair-vertices-hydrocarbon → UU lzero
  edge-hydrocarbon = edge-Undirected-Graph-𝔽 finite-graph-hydrocarbon

  is-finite-edge-hydrocarbon :
    (p : unordered-pair-vertices-hydrocarbon) → is-finite (edge-hydrocarbon p)
  is-finite-edge-hydrocarbon =
    is-finite-edge-Undirected-Graph-𝔽 finite-graph-hydrocarbon

  carbon-atom-hydrocarbon :
    vertex-hydrocarbon → tetrahedron-in-3-space
  carbon-atom-hydrocarbon = pr1 (pr2 H)

  electron-carbon-atom-hydrocarbon :
    (c : vertex-hydrocarbon) → UU lzero
  electron-carbon-atom-hydrocarbon c =
    vertex-tetrahedron-in-3-space (carbon-atom-hydrocarbon c)
```
