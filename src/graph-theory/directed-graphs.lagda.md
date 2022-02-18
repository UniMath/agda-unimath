---
title: Formalisation of the Symmetry Book
---

```agda
{-# OPTIONS --without-K --exact-split --allow-unsolved-metas #-}

module graph-theory.directed-graphs where

open import univalent-foundations public

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
