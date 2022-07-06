---
title: Univalent type families
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation.univalent-type-families where

open import foundation.equivalences using (is-equiv)
open import foundation.identity-types using (_＝_; equiv-tr)
open import foundation.universe-levels using (Level; UU; _⊔_)
```

## Idea

A type family `B` over `A` is said to be univalent if the map

```md
  equiv-tr : (Id x y) → (B x ≃ B y)
```

is an equivalence for every `x y : A`.

## Definition

```agda
is-univalent :
  {l1 l2 : Level} {A : UU l1} → (A → UU l2) → UU (l1 ⊔ l2)
is-univalent {A = A} B = (x y : A) → is-equiv (λ (p : x ＝ y) → equiv-tr B p)
```
