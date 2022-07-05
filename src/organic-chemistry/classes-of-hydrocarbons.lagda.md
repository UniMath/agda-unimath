---
title: Classes of hydrocarbons
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module organic-chemistry.classes-of-hydrocarbons where

open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.natural-numbers


open import finite-group-theory.tetrahedra-in-3-space

open import foundation.propositional-truncations
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.mere-equivalences
open import foundation.universe-levels
open import foundation.unordered-pairs
open import foundation.propositions
open import foundation.embeddings

open import graph-theory.connected-undirected-graphs
open import graph-theory.finite-graphs

open import univalent-combinatorics.finite-types

open import organic-chemistry.hydrocarbons
```

## Idea

We define the three major classes of hydrocarbons: Alkanes, alkenes, and alkynes. These are distinguished by the _saturation_ of their carbon atoms, i.e., by the absence or presence of double (or triple) carbon-carbon bonds.

Chemically, a carbon atom is called **saturated** when all of its four valence electrons are shared with _different_ atoms; otherwise, it is called unsaturated. An **alkane** is a hydrocarbon with only saturated carbons, an **alkene** is a hydrocarbon with at least one carbon-carbon double bond, and an **alkyne** has at least one carbon-carbon triple bond.

## Definition

```agda
module _ (H : hydrocarbon) where
  is-saturated-carbon-hydrocarbon : vertex-hydrocarbon H → UU
  is-saturated-carbon-hydrocarbon c =
      (c' : vertex-hydrocarbon H)
    → is-prop (edge-hydrocarbon H (standard-unordered-pair c c'))
```

Type-theoretically, the saturation condition on a carbon atom (fix one and call it `c`) is incarnated by asking that, for every other carbon atom `c'`, the type of edges `c --- c'` is a proposition. Since edges incident on `c` are a subtype of the type representing electrons of `c`, this guarantees that `c` shares no more than 1 electron with any other carbon in the structure. An **alkane** is a hydrocarbon such that every carbon is saturated.

```agda
  is-alkane-hydrocarbon : UU
  is-alkane-hydrocarbon = ∀ c → is-saturated-carbon-hydrocarbon c
```

We refer to a hydrocarbon equipped with a choice of $n$ carbons equipped with double bonds as an "n-alkene". For an n-alkene, the embedding from the given type (the first component of the n-alkene structure) specifies which carbons have double bonds. For example, 1-butene and but-2-ene have the same geometry, and the embedding is what differentiates them (while the third tautometer, isobutylene, is branched, thus has a different geometry).

```agda
  has-double-bond : vertex-hydrocarbon H → UU
  has-double-bond c = type-trunc-Prop (Σ (vertex-hydrocarbon H) λ c' →
    has-cardinality 2 (edge-hydrocarbon H (standard-unordered-pair c c')))

  n-alkene : ℕ → UU (lsuc lzero)
  n-alkene n =
    Σ (UU-Fin n) λ carbons →
      Σ (type-UU-Fin carbons ↪ vertex-hydrocarbon H) λ embed-carbons →
        (c : type-UU-Fin carbons) → has-double-bond (pr1 embed-carbons c)
```

The definition of n-alkynes is analogous.

```agda
  has-triple-bond : vertex-hydrocarbon H → UU
  has-triple-bond c = type-trunc-Prop (Σ (vertex-hydrocarbon H) λ c' →
    has-cardinality 3 (edge-hydrocarbon H (standard-unordered-pair c c')))

  n-alkyne : ℕ → UU (lsuc lzero)
  n-alkyne n =
    Σ (UU-Fin n) λ carbons →
      Σ (type-UU-Fin carbons ↪ vertex-hydrocarbon H) λ embed-carbons →
        (c : type-UU-Fin carbons) → has-triple-bond (pr1 embed-carbons c)
```
