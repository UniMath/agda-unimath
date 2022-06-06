# Species

```agda
{-# OPTIONS --without-K --exact-split #-}

module univalent-combinatorics.species where

open import foundation.universe-levels using (Level; UU; lsuc)

open import univalent-combinatorics.finite-types using (𝔽)
```

### Idea

In this file, we define the type of species. A species is just a
map from 𝔽 to a universe.

## Definition

```agda
species : (l : Level) → UU (lsuc l)
species l = 𝔽 → UU l
```
