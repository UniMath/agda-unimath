# Nontrivial rings

```agda
{-# OPTIONS --without-K --exact-split #-}

module ring-theory.nontrivial-rings where

open import foundation.identity-types using (Id)
open import foundation.negation using (¬)
open import foundation.universe-levels using (Level; UU)

open import ring-theory.rings using (Ring; zero-Ring; unit-Ring)
```

## Idea

Nontrivial rings are rings in which `0 ≠ 1`.

## Definition

```agda
is-nontrivial-Ring :
  { l : Level} → Ring l → UU l
is-nontrivial-Ring R = ¬ (Id (zero-Ring R) (unit-Ring R))
```
