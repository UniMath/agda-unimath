---
title: Complements of type families
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation.complements where

open import foundation.dependent-pair-types using (Σ)
open import foundation.empty-types using (is-empty)
open import foundation.functions using (_∘_)
open import foundation.universe-levels using (Level; UU; _⊔_)
```

## Idea

The complement of a type family `B` over `A` consists of the type of points in `A` at which `B x` is empty.

```agda
complement :
  {l1 l2 : Level} {A : UU l1} (B : A → UU l2) → UU (l1 ⊔ l2)
complement {l1} {l2} {A} B = Σ A (is-empty ∘ B)
```
