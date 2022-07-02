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

open import graph-theory.finite-graphs

open import univalent-combinatorics.finite-types
```

## Idea

We define the type of all theoretically possible hydrocarbons, correctly accounting for the symmetries between hydrocarbons and the different isomers.

Hydrocarbons are built out of carbon and hydrogen atoms. The symmetry group of an isolated carbon atom in 3-space is the alternating group `A₄`, where the number 4 comes from the number of bonds a carbon atom makes in a molecule.

Bonds in hydrocarbons can appear as single bonds, double bonds, and triple bonds, but there are no quadruple bonds. 

## Definition

```agda
hydrocarbon : UU (lsuc lzero)
hydrocarbon =
  Σ ( Graph-𝔽)
    ( λ G →
      Σ ( vertex-Graph-𝔽 G → tetrahedron-in-3-space)
        ( λ C →
          ( ( c : vertex-Graph-𝔽 G) →
            Σ ( vertex-Graph-𝔽 G)
              ( λ c' →
                edge-Graph-𝔽 G
                  ( standard-unordered-pair c c')) ↪
              type-UU-Fin (pr1 (C c))) ×
          ( ( (c : vertex-Graph-𝔽 G) →
              ¬ ( edge-Graph-𝔽 G
                  ( standard-unordered-pair c c))) ×
            ( (c c' : vertex-Graph-𝔽 G) →
              leq-ℕ (number-of-elements-is-finite (is-finite-type-𝔽 (pr2 G (standard-unordered-pair c c')))) 3))))
```
