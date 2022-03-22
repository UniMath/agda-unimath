# Directed graphs

```agda
{-# OPTIONS --without-K --exact-split #-}

module graph-theory.directed-graphs where

open import foundation.universe-levels
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.functions
open import foundation.identity-types
```

## Idea

A graph consists of a type of vertices equipped with a binary, type valued relation of edges.

## Definition

```agda
Graph : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
Graph l1 l2 = Σ (UU l1) (λ V → V → V → UU l2)

module _
  {l1 l2 : Level} (G : Graph l1 l2)
  where

  vertex-Graph : UU l1
  vertex-Graph = pr1 G

  edge-Graph : vertex-Graph → vertex-Graph → UU l2
  edge-Graph = pr2 G
```

### Alternative definition

```agda
module alternative where

  Graph' : (l1 l2 : Level)  → UU (lsuc l1 ⊔ lsuc l2)
  Graph' l1 l2 = Σ (UU l1)  λ V → Σ (UU l2) (λ E → (E → V) × (E → V))
  -- TODO: Add the syntax ∑[ x ]

  module _ {l1 l2 : Level} (G : Graph' l1 l2) where

    vertex-Graph' : UU l1
    vertex-Graph' = pr1 G

    edge-Graph' : UU l2
    edge-Graph' = pr1 (pr2 G)

    source-edge-Graph : edge-Graph' -> vertex-Graph'
    source-edge-Graph = pr1 (pr2 (pr2 G))

    target-edge-Graph : edge-Graph' -> vertex-Graph'
    target-edge-Graph = pr2 (pr2 (pr2 G))
```

```agda
module equiv {l1 l2 : Level} where
  open alternative

  Graph-to-Graph' : Graph l1 l2 -> Graph' l1 (l1 ⊔ l2)
  pr1 (Graph-to-Graph' G) = vertex-Graph G
  pr1 (pr2 (Graph-to-Graph' G))
    = Σ (vertex-Graph G) (λ x → Σ (vertex-Graph G) λ y → edge-Graph G  x y)
  pr1 (pr2 (pr2 (Graph-to-Graph' G))) = pr1
  pr2 (pr2 (pr2 (Graph-to-Graph' G))) = pr1 ∘ pr2

  Graph'-to-Graph : Graph' l1 l2 -> Graph l1 (l1 ⊔ l2)
  Graph'-to-Graph (pair V (pair E (pair st tg)))
    = pair V λ x y → Σ E λ e → (Id (st e) x) × (Id (tg e) y)

-- TODO: One can show that the two definitions (Graph and Graph') are equivalent
-- when the underlying types for vertices and edges are sets. I'm not quite sure
-- if it still holds after removing such an assumption, as it was used to show the equiv here
-- https://jonaprieto.github.io/synthetic-graph-theory/lib.graph-definitions.Alternative-definition-is-equiv.html#2371
```