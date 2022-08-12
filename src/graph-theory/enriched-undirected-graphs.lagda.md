---
title: Enriched undirected graphs
---

```agda
module graph-theory.enriched-undirected-graphs where

open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.universe-levels

open import graph-theory.incidence-undirected-graphs
open import graph-theory.undirected-graphs
```

## Idea

Consider a type `A` equipped with a type family `B` over `A`. An **`(A,B)`-enriched undirected graph** is an undirected graph `G := (V,E)` equipped with a map `f : V → A`, and for each vertex `v` an equivalence from `B (f v)` to the type of all vertices `w` equipped with an edge between `v` and `w`.

## Definition

```agda 
Enriched-Undirected-Graph :
  {l1 l2 : Level} (l3 l4 : Level) (A : UU l1) (B : A → UU l2) →
  UU (l1 ⊔ l2 ⊔ lsuc l3 ⊔ lsuc l4)
Enriched-Undirected-Graph l3 l4 A B =
  Σ ( Undirected-Graph l3 l4)
    ( λ G →
      Σ ( vertex-Undirected-Graph G → A)
        ( λ f →
          ( x : vertex-Undirected-Graph G) →
          B (f x) ≃ incidence-Undirected-Graph G x))
```
