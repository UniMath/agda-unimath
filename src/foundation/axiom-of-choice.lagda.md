---
title: The axiom of choice
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation.axiom-of-choice where

open import foundation.propositional-truncations using (type-trunc-Prop)
open import foundation.sets using (Set; type-Set)
open import foundation.universe-levels using (Level; UU; lsuc; _⊔_)
```

## Idea

The axiom of choice asserts that for every family of inhabited types indexed by a set, the type of sections of that family is inhabited.

## Definition

```agda
AC : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
AC l1 l2 =
  (A : Set l1) (B : type-Set A → Set l2) →
  ((x : type-Set A) → type-trunc-Prop (type-Set (B x))) →
  type-trunc-Prop ((x : type-Set A) → type-Set (B x))
```
