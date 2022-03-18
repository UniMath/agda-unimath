# The maybe modality on finite types

```agda
{-# OPTIONS --without-K --exact-split #-}

module univalent-combinatorics.maybe where

open import foundation.maybe public

open import elementary-number-theory.natural-numbers using (ℕ; zero-ℕ; succ-ℕ)

open import foundation.universe-levels using (Level)

open import univalent-combinatorics.coproduct-types using
  ( coprod-UU-Fin-Level)
open import univalent-combinatorics.finite-types using
  ( UU-Fin-Level; UU-Fin; unit-UU-Fin)
```

```agda
add-free-point-UU-Fin-Level :
  {l1 : Level} {k : ℕ} → UU-Fin-Level l1 k → UU-Fin-Level l1 (succ-ℕ k)
add-free-point-UU-Fin-Level X = coprod-UU-Fin-Level X unit-UU-Fin

add-free-point-UU-Fin : {k : ℕ} → UU-Fin k → UU-Fin (succ-ℕ k)
add-free-point-UU-Fin X = add-free-point-UU-Fin-Level X
```
