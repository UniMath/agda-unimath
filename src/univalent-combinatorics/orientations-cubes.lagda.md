---
title: Orientations of cubes
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module univalent-combinatorics.orientations-cubes where

open import elementary-number-theory.natural-numbers using (ℕ; zero-ℕ; succ-ℕ)

open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.identity-types using (Id)
open import foundation.iterating-functions using (iterate)
open import foundation.universe-levels using (UU; lzero)

open import univalent-combinatorics.cubes using
  ( cube; vertex-cube; is-finite-dim-cube; is-finite-axis-cube)
open import univalent-combinatorics.dependent-sum-finite-types using
  ( is-finite-Σ)
open import univalent-combinatorics.equality-finite-types using
  ( is-finite-eq; has-decidable-equality-is-finite)
open import univalent-combinatorics.finite-types using
  ( number-of-elements-is-finite; is-finite-empty)
open import univalent-combinatorics.function-types using
  ( is-finite-function-type)
open import univalent-combinatorics.standard-finite-types using
  ( Fin; succ-Fin)
```

## Definition

```agda
orientation-cube : {k : ℕ} → cube k → UU (lzero)
orientation-cube {k} X =
  Σ ( vertex-cube k X → Fin 2)
    ( λ h →
      ( x y : vertex-cube k X) →
        Id ( iterate
             ( number-of-elements-is-finite
               ( is-finite-Σ
                 ( is-finite-dim-cube k X)
                 ( λ d →
                   is-finite-function-type
                     ( is-finite-eq
                       ( has-decidable-equality-is-finite
                         ( is-finite-axis-cube k X d))
                     { x d}
                     { y d})
                     ( is-finite-empty))))
             ( succ-Fin 2)
             ( h x))
           ( h y))
```
