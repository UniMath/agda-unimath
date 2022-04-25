---
title: Σ-decompositions of types
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation.sigma-decompositions where

open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.mere-equivalences
open import foundation.propositional-truncations
open import foundation.universe-levels
```

## Idea

The type of Σ-decompositions of a type `A` is the type of types `X` equipped with a type family `Y` on `X` such that `Σ X Y` is merely equivalent to `A`.

## Definition

```agda
decomposition-Σ :
  {l1 : Level} (l2 l3 : Level) (A : UU l1) → UU (l1 ⊔ lsuc l2 ⊔ lsuc l3)
decomposition-Σ l2 l3 A =
  Σ ( UU l2)
    ( λ X →
      Σ ( X → UU l3)
        ( λ Y →
          ((x : X) → type-trunc-Prop (Y x)) × mere-equiv A (Σ X Y)))

module _
  {l1 l2 l3 : Level} {A : UU l1} (D : decomposition-Σ l2 l3 A)
  where
  
  indexing-type-decomposition-Σ : UU l2
  indexing-type-decomposition-Σ = pr1 D
```
