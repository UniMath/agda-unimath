---
title: Petri-nets
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module univalent-combinatorics.petri-nets where

open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import univalent-combinatorics.finite-types
```

## Idea

We give a definition of Petri nets due to Joachim Kock [[1]][1]

## Definition

```agda
Petri-Net : UU (lsuc lzero)
Petri-Net =
  Σ 𝔽 (λ S → Σ 𝔽 (λ T → (type-𝔽 S → type-𝔽 T → 𝔽) × (type-𝔽 T → type-𝔽 S → 𝔽)))

module _
  (P : Petri-Net)
  where

  place-Petri-Net-𝔽 : 𝔽
  place-Petri-Net-𝔽 = pr1 P

  place-Petri-Net : UU lzero
  place-Petri-Net = type-𝔽 place-Petri-Net-𝔽

  transition-Petri-Net-𝔽 : 𝔽
  transition-Petri-Net-𝔽 = pr1 (pr2 P)

  transition-Petri-Net : UU lzero
  transition-Petri-Net = type-𝔽 transition-Petri-Net-𝔽

  incoming-arc-Petri-Net-𝔽 : place-Petri-Net → transition-Petri-Net → 𝔽
  incoming-arc-Petri-Net-𝔽 = pr1 (pr2 (pr2 P))

  incoming-arc-Petri-Net : place-Petri-Net → transition-Petri-Net → UU lzero
  incoming-arc-Petri-Net s t = type-𝔽 (incoming-arc-Petri-Net-𝔽 s t)

  outgoing-arc-Petri-Net-𝔽 : transition-Petri-Net → place-Petri-Net → 𝔽
  outgoing-arc-Petri-Net-𝔽 = pr2 (pr2 (pr2 P))

  outgoing-arc-Petri-Net : transition-Petri-Net → place-Petri-Net → UU lzero
  outgoing-arc-Petri-Net t s = type-𝔽 (outgoing-arc-Petri-Net-𝔽 t s)
```

[1]: <https://arxiv.org/abs/2005.05108>
