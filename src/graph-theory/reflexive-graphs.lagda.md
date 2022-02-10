---
title: Formalisation of the Symmetry Book
---

```agda
{-# OPTIONS --without-K --exact-split --allow-unsolved-metas #-}

module graph-theory.reflexive-graphs where

open import univalent-foundations public

Reflexive-Graph : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
Reflexive-Graph l1 l2 =
  Σ (UU l1) (λ V → Σ (V → V → UU l2) (λ E → (v : V) → E v v))

module _
  {l1 l2 : Level} (G : Reflexive-Graph l1 l2)
  where

  vertex-Reflexive-Graph : UU l1
  vertex-Reflexive-Graph = pr1 G

  edge-Reflexive-Graph : vertex-Reflexive-Graph → vertex-Reflexive-Graph → UU l2
  edge-Reflexive-Graph = pr1 (pr2 G)

  refl-Reflexive-Graph : (x : vertex-Reflexive-Graph) → edge-Reflexive-Graph x x
  refl-Reflexive-Graph = pr2 (pr2 G)

```
