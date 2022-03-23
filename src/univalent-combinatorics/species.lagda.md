# Species

```agda
{-# OPTIONS --without-K --exact-split #-}

module univalent-combinatorics.species where

open import foundation.universe-levels using (Level; UU; lsuc)

open import univalent-combinatorics.finite-types using (𝔽)
```

## Definition

```agda
species : (l : Level) → UU (lsuc l)
species l = 𝔽 → UU l
```
