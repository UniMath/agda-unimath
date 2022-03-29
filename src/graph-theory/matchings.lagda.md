# Matchings

```agda
{-# OPTIONS --without-K --exact-split #-}

module graph-theory.matchings where

open import foundation.contractible-types using (is-contr)
open import foundation.coproduct-types using (inr)
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.identity-types using (Id)
open import foundation.propositions using (is-prop)
open import foundation.unit-type using (star)
open import foundation.universe-levels using (Level; UU; _⊔_; lsuc; lzero)
open import foundation.unordered-pairs using (standard-unordered-pair)

open import graph-theory.edge-coloured-undirected-graphs using
  ( incidence-edge-colouring-Undirected-Graph)
open import graph-theory.incidence-undirected-graphs using
  ( incidence-Undirected-Graph)
open import graph-theory.undirected-graphs using
  ( Undirected-Graph; unordered-pair-vertices-Undirected-Graph;
    vertex-Undirected-Graph; edge-Undirected-Graph)

open import univalent-combinatorics.standard-finite-types using (Fin)
```

## Idea

A matching in a undirected graph is a set of edges without common vertices. 

## Definitions

```agda
module _
  {l1 l2 : Level}
  where

  selected-edges-vertex-Undirected-Graph :
    ( G : Undirected-Graph l1 l2) →
    ( (p : unordered-pair-vertices-Undirected-Graph G) →
      edge-Undirected-Graph G p → Fin 2) →
    vertex-Undirected-Graph G → UU (l1 ⊔ l2)
  selected-edges-vertex-Undirected-Graph G c x =
    Σ ( vertex-Undirected-Graph G)
      ( λ y →
        Σ ( edge-Undirected-Graph G (standard-unordered-pair x y))
          ( λ e → Id (c (standard-unordered-pair x y) e) (inr star)))

  matching : Undirected-Graph l1 l2 → UU (lsuc lzero ⊔ l1 ⊔ l2)
  matching G =
    Σ ( (p : unordered-pair-vertices-Undirected-Graph G) →
        edge-Undirected-Graph G p → Fin 2)
      ( λ c →
        ( x : vertex-Undirected-Graph G) →
        is-prop (selected-edges-vertex-Undirected-Graph G c x))

  perfect-matching : Undirected-Graph l1 l2 → UU (lsuc lzero ⊔ l1 ⊔ l2)
  perfect-matching G =
    Σ ( (p : unordered-pair-vertices-Undirected-Graph G) →
        edge-Undirected-Graph G p → Fin 2)
      ( λ c →
        ( x : vertex-Undirected-Graph G) →
          is-contr (selected-edges-vertex-Undirected-Graph G c x))
```
