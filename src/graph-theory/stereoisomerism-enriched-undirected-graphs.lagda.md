---
title: Stereoisomerism for enriched undirected graphs
---

```agda
module graph-theory.stereoisomerism-enriched-undirected-graphs where

open import foundation.universe-levels

open import graph-theory.enriched-undirected-graphs
open import graph-theory.equivalences-undirected-graphs
```

## Idea

A stereoisomerism between two `(A,B)`-enriched undirected graphs is an equivalence between their underlying undirected graphs. This concept is derived from the concept of stereoisomerism of chemical compounds.

## Definition

```agda
module _
  {l1 l2  l3 l4 l5 l6 : Level} (A : UU l1) (B : A → UU l2)
  (G : Enriched-Undirected-Graph l3 l4 A B)
  (H : Enriched-Undirected-Graph l5 l6 A B)
  where

  stereoisomerism-Enriched-Undirected-Graph :
    UU (lsuc lzero ⊔ l3 ⊔ l4 ⊔ l5 ⊔ l6)
  stereoisomerism-Enriched-Undirected-Graph =
    equiv-Undirected-Graph
      ( undirected-graph-Enriched-Undirected-Graph A B G)
      ( undirected-graph-Enriched-Undirected-Graph A B H)
```
