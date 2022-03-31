# Vertex covers

```agda
{-# OPTIONS --without-K --exact-split #-}

module graph-theory.vertex-covers where

open import foundation.cartesian-product-types using (_×_)
open import foundation.coproduct-types using (inr)
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.identity-types using (Id)
open import foundation.propositional-truncations using (type-trunc-Prop)
open import foundation.propositions using (is-prop)
open import foundation.unit-type using (star)
open import foundation.universe-levels using (Level; UU; _⊔_; lsuc; lzero)
open import foundation.unordered-pairs using (is-in-unordered-pair)

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

A vertex cover is a set of vertices that includes at least one extremity of each edges

## Definitions

```agda
vertex-cover : {l1 l2 : Level} → Undirected-Graph l1 l2 →
  UU (lsuc lzero ⊔ l1 ⊔ l2)
vertex-cover G = 
  Σ ( vertex-Undirected-Graph G → Fin 2)
    ( λ c →
      ( p : unordered-pair-vertices-Undirected-Graph G) → edge-Undirected-Graph G p →
        type-trunc-Prop
          ( Σ (vertex-Undirected-Graph G)
            ( λ x → is-in-unordered-pair p x × Id (c x) (inr star))))
```
