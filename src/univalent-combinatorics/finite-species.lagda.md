# Finite species

```agda
{-# OPTIONS --without-K --exact-split #-}

module univalent-combinatorics.finite-species where

open import foundation.universe-levels using (UU)

open import univalent-combinatorics.finite-types using (𝔽)
```

## Definition

```agda
finite-species : UU₁
finite-species = 𝔽 → 𝔽
```