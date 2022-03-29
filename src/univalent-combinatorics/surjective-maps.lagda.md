---
title: Surjective maps between finite types
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module univalent-combinatorics.surjective-maps where

open import foundation.surjective-maps public

open import foundation.decidable-types using (is-decidable)
open import foundation.universe-levels using (Level; UU)

open import univalent-combinatorics.decidable-dependent-function-types using
  ( is-decidable-Π-is-finite)
open import univalent-combinatorics.fibers-of-maps-between-finite-types
open import univalent-combinatorics.finite-types using
  ( is-finite; is-decidable-type-trunc-Prop-is-finite)
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
