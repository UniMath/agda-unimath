---
title: Alcohols
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module organic-chemistry.alcohols where

open import foundation.cartesian-product-types
open import foundation.decidable-subtypes
open import foundation.dependent-pair-types
open import foundation.negation
open import foundation.propositional-truncations
open import foundation.universe-levels
open import foundation.unordered-pairs

open import organic-chemistry.hydrocarbons
```

## Idea

An alcohol is a hydrocarbon with at least one `-OH` group. The type of alcohols can therefore be defined as the type of hydrocarbons equipped with a distinguished subset of the available (unbonded) electrons of the carbon atoms.

## Definition

```agda
alcohol : UU (lsuc lzero)
alcohol =
  Σ ( hydrocarbon)
    ( λ X →
      Σ ( (c : vertex-hydrocarbon X) →
          decidable-subtype lzero (electron-carbon-atom-hydrocarbon X c))
        ( λ OH →
          ( ( c c' : vertex-hydrocarbon X) →
            ( b : edge-hydrocarbon X (standard-unordered-pair c c')) →
            ¬ (is-in-decidable-subtype (OH c) (bonding-hydrocarbon X b))) ×
          ( type-trunc-Prop
            ( Σ ( vertex-hydrocarbon X)
                ( λ c → type-decidable-subtype (OH c))))))
```
