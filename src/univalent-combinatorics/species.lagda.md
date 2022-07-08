---
title: Species
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module univalent-combinatorics.species where

open import foundation.equivalences
open import foundation.identity-types
open import foundation.universe-levels

open import univalent-combinatorics.finite-types
```

### Idea

In this file, we define the type of species. A species is just a
map from 𝔽 to a universe.

## Definitions

### Species

```agda
species : (l : Level) → UU (lsuc l)
species l = 𝔽 → UU l
```

### Transport in species

```agda
tr-species :
  {l : Level} (F : species l) (X Y : 𝔽) → type-𝔽 X ≃ type-𝔽 Y → F X → F Y
tr-species F X Y e = tr F (eq-equiv-𝔽 X Y e)
```
