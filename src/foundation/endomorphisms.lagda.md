---
title: endomorphisms
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation.endomorphisms where

open import foundation.universe-levels using (Level; UU)
```

## Idea

An endomorphism on a type `A` is a map `A → A`.

## Definitions

### Endomorphisms

```agda
endo : {l : Level} → UU l → UU l
endo A = A → A
```
