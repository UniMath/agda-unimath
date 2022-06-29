---
title: Multisubsets
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation.multisubsets where

open import elementary-number-theory.natural-numbers using (ℕ; zero-ℕ)

open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.fibers-of-maps using (fib)
open import foundation.identity-types using (_＝_)
open import foundation.images using (im)
open import foundation.negation using (¬)
open import foundation.sets using (UU-Set; type-Set)
open import foundation.universe-levels using (Level; UU; lsuc; _⊔_)

open import univalent-combinatorics.finite-types using (is-finite)
```

## Idea

A multisubset of a given set `U` is a type `B` equipped with a function `f : B → U`

## Definition

```agda
module _
  {l1 : Level} (l2 : Level)
  where

  multisubset : UU-Set l1 → UU (l1 ⊔ lsuc l2)
  multisubset U = Σ (UU l2) (λ B → B → type-Set U)

  is-locally-finite-multisubset :
    (U : UU-Set l1) → multisubset U → UU (l1 ⊔ l2)
  is-locally-finite-multisubset U (pair B f) =
    (x : type-Set U) → is-finite (fib f x)

  is-finite-multisubset :
    (U : UU-Set l1) → multisubset U → UU (l1 ⊔ l2)
  is-finite-multisubset U (pair B f) = is-finite (im f)

module _
  {l1 : Level}
  where

  locally-finite-multisubset : UU-Set l1 → UU l1
  locally-finite-multisubset U = type-Set U → ℕ

  support-locally-finite-multisubset : 
    (U : UU-Set l1) → locally-finite-multisubset U → UU l1
  support-locally-finite-multisubset U μ =
    Σ (type-Set U) λ x → ¬ (μ x ＝ zero-ℕ)

  is-finite-locally-finite-multisubset :
    (U : UU-Set l1) → locally-finite-multisubset U → UU l1
  is-finite-locally-finite-multisubset U μ =
    is-finite (support-locally-finite-multisubset U μ)
```
