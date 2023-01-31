---
title: Surjective maps between finite types
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module univalent-combinatorics.surjective-maps where

open import foundation.surjective-maps public

open import foundation.decidable-types
open import foundation.universe-levels

open import univalent-combinatorics.decidable-dependent-function-types using
  ( is-decidable-Π-is-finite)
open import univalent-combinatorics.fibers-of-maps using (is-finite-fib)
open import univalent-combinatorics.finite-types
```

## Properties

```agda
is-decidable-is-surjective-is-finite :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  is-finite A → is-finite B → is-decidable (is-surjective f)
is-decidable-is-surjective-is-finite f HA HB =
  is-decidable-Π-is-finite HB
    ( λ y → is-decidable-type-trunc-Prop-is-finite (is-finite-fib f HA HB y))
```
