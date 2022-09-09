---
title: The maybe modality on finite types
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module univalent-combinatorics.maybe where

open import foundation.maybe public

open import elementary-number-theory.natural-numbers using (ℕ; zero-ℕ; succ-ℕ)

open import foundation.universe-levels using (Level)

open import univalent-combinatorics.coproduct-types using
  ( coprod-UU-Fin)
open import univalent-combinatorics.finite-types using
  ( UU-Fin; unit-UU-Fin)
```

```agda
add-free-point-UU-Fin :
  {l1 : Level} (k : ℕ) → UU-Fin l1 k → UU-Fin l1 (succ-ℕ k)
add-free-point-UU-Fin k X = coprod-UU-Fin k 1 X unit-UU-Fin
```
