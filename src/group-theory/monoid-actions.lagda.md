---
title: Monoid actions
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module group-theory.monoid-actions where

open import foundation.dependent-pair-types
open import foundation.universe-levels

open import group-theory.monoids

open import structured-types.wild-monoids
```

## Idea

A monoid `M` can act on a type `A` by a monoid homomorphism `hom M (A → A)`.

## Definition

### Wild monoid actions

```agda
module _
  {l1 : Level} (M : Wild-Monoid l1)
  where

  Wild-Monoid-Action : (l : Level) → UU (l1 ⊔ lsuc l)
  Wild-Monoid-Action l = Σ (UU l) (λ X → type-Wild-Monoid M → X → X)
```

### Monoid actions

```agda
module _
  {l1 : Level} (M : Monoid l1)
  where

  Monoid-Action : (l : Level) → UU (l1 ⊔ lsuc l)
  Monoid-Action l = Σ (UU l) (λ X → type-Monoid M → X → X)
```
