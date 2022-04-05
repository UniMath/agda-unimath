---
title: Subsets of rings
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module ring-theory.subsets-rings where

open import foundation.propositional-extensionality using (is-set-UU-Prop)
open import foundation.sets using (is-set; is-set-function-type)
open import foundation.subtypes using (subtype)
open import foundation.universe-levels using (Level; UU; _⊔_; lsuc)

open import ring-theory.rings using (Ring; type-Ring)
```

## Idea

A subset of a ring is a subtype of the underlying type of a ring

## Definition

```agda
subset-Ring :
  (l : Level) {l1 : Level} (R : Ring l1) → UU ((lsuc l) ⊔ l1)
subset-Ring l R = subtype l (type-Ring R)

is-set-subset-Ring :
  (l : Level) {l1 : Level} (R : Ring l1) → is-set (subset-Ring l R)
is-set-subset-Ring l R =
  is-set-function-type is-set-UU-Prop
```
