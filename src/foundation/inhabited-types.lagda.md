---
title: Inhabited types
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation.inhabited-types where

open import foundation.dependent-pair-types
open import foundation.propositional-truncations
open import foundation.universe-levels
```

## Idea

Inhabited types are types equipped with an element of its propositional truncation.

## Definition

```agda
Inhabited-Type : (l : Level) → UU (lsuc l)
Inhabited-Type l = Σ (UU l) type-trunc-Prop

module _
  {l : Level} (X : Inhabited-Type l)
  where

  type-Inhabited-Type : UU l
  type-Inhabited-Type = pr1 X

  is-inhabited-type-Inhabited-Type : type-trunc-Prop type-Inhabited-Type
  is-inhabited-type-Inhabited-Type = pr2 X
```
