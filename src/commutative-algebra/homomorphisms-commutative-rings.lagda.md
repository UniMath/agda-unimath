---
title: Homomorphisms of commutative rings
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module commutative-algebra.homomorphisms-commutative-rings where

open import commutative-algebra.commutative-rings using
  ( Commutative-Ring; ring-Commutative-Ring)

open import foundation.universe-levels using (Level; UU; _⊔_)

open import ring-theory.homomorphisms-rings using (type-hom-Ring)
```

## Idea

A morphism of commutative rings is just a morphism between their underlying rings.

## Definition

```agda
type-hom-Commutative-Ring :
  { l1 l2 : Level} → Commutative-Ring l1 → Commutative-Ring l2 → UU (l1 ⊔ l2)
type-hom-Commutative-Ring R1 R2 =
  type-hom-Ring (ring-Commutative-Ring R1) (ring-Commutative-Ring R2)
```
