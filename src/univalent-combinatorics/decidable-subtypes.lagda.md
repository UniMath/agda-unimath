---
title: Decidable subtypes of finite types
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module univalent-combinatorics.decidable-subtypes where

open import foundation.decidable-subtypes public

open import foundation.decidable-propositions using
  ( prop-decidable-Prop; is-decidable-type-decidable-Prop)
open import foundation.universe-levels using (Level; UU)

open import univalent-combinatorics.dependent-sum-finite-types using
  ( is-finite-Σ)
open import univalent-combinatorics.finite-types using
  ( is-finite; is-finite-is-decidable-Prop)
```

## Idea

Decidable subtypes of finite types are finite.

## Properties

```agda
module _
  {l1 l2 : Level} {X : UU l1} (P : decidable-subtype l2 X)
  where

  abstract
    is-finite-decidable-subtype :
      is-finite X → is-finite (type-decidable-subtype P)
    is-finite-decidable-subtype H =
      is-finite-Σ H
        ( λ x →
          is-finite-is-decidable-Prop
            ( prop-decidable-Prop (P x))
            ( is-decidable-type-decidable-Prop (P x)))
```
