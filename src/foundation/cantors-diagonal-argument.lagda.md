---
title: Cantor's diagonal argument
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation.cantors-diagonal-argument where

open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.empty-types using (empty; empty-Prop)
open import foundation.fibers-of-maps using (fib)
open import foundation.function-extensionality using (htpy-eq)
open import foundation.logical-equivalences using (iff-eq)
open import foundation.negation using (neg-Prop; no-fixed-points-neg-Prop; ¬)
open import foundation.propositional-truncations using
  ( apply-universal-property-trunc-Prop)
open import foundation.propositions using (UU-Prop)
open import foundation.surjective-maps using (is-surjective)
open import foundation.universe-levels using (Level; UU)
```

## Idea

Cantor's diagonal argument is used to show that there is no surjective map from a type into the type of its subtypes.

## Theorem

```agda
map-cantor :
  {l1 l2 : Level} (X : UU l1) (f : X → (X → UU-Prop l2)) → (X → UU-Prop l2)
map-cantor X f x = neg-Prop (f x x)

abstract
  not-in-image-map-cantor :
    {l1 l2 : Level} (X : UU l1) (f : X → (X → UU-Prop l2)) →
    ( t : fib f (map-cantor X f)) → empty
  not-in-image-map-cantor X f (pair x α) =
    no-fixed-points-neg-Prop (f x x) (iff-eq (htpy-eq α x))

abstract
  cantor : {l1 l2 : Level} (X : UU l1) (f : X → (X → UU-Prop l2)) →
    ¬ (is-surjective f)
  cantor X f H =
    ( apply-universal-property-trunc-Prop
      ( H (map-cantor X f))
      ( empty-Prop)
      ( not-in-image-map-cantor X f))
```
