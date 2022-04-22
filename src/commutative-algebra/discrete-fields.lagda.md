---
title: Discrete fields
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module commutative-algebra.discrete-fields where

open import commutative-algebra.commutative-rings using
  ( Comm-Ring; ring-Comm-Ring)

open import foundation.universe-levels using (Level; UU)

open import ring-theory.division-rings using (is-division-Ring)
```

## Idea

A discrete field is a commutative division ring. They are called discrete, because only nonzero elements are assumed to be invertible.

## Definition

```agda
is-discrete-field-Comm-Ring :
  { l : Level} → Comm-Ring l → UU l
is-discrete-field-Comm-Ring R = is-division-Ring (ring-Comm-Ring R)
```
