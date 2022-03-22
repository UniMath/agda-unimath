# Incidence in undirected graphs

```agda
{-# OPTIONS --without-K --exact-split #-}

module graph-theory.incidence-undirected-graphs where

open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.universe-levels using (Level; UU; _⊔_)
open import foundation.unordered-pairs using (standard-unordered-pair)

open import graph-theory.undirected-graphs using
  ( Undirected-Graph; vertex-Undirected-Graph; edge-Undirected-Graph)
```

## Idea

The type of edges incident to a vertex `x` of an undirected graph is the total space of all edges between `x` and any vertex.

## Definition

```agda
module _
  {l1 l2 : Level} (G : Undirected-Graph l1 l2)
  where

  incidence-Undirected-Graph : vertex-Undirected-Graph G → UU (l1 ⊔ l2)
  incidence-Undirected-Graph x =
    Σ ( vertex-Undirected-Graph G)
      ( λ y → edge-Undirected-Graph G (standard-unordered-pair x y))
```

