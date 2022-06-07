---
title: Propositional resizing
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation.propositional-resizing where

open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.propositions
open import foundation.universe-levels
```

## Idea

We say that there is propositional resizing for propositions of universe levels `l1` and `l2` if there is an equivalence `e : UU-Prop l1 ≃ UU-Prop l2` such that for any proposition `P : UU-Prop l1` we have `P ↔ e P`.

## Definition

```agda
propositional-resizing : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
propositional-resizing l1 l2 =
  Σ ( UU-Prop l1 ≃ UU-Prop l2)
    ( λ e → (P : UU-Prop l1) → type-Prop P ≃ type-Prop (map-equiv e P))
```
