---
title: Type arithmetic with the booleans
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation.type-arithmetic-booleans where

open import foundation.booleans using (bool; true; false)
open import foundation.coproduct-types using (_+_; inl; inr)
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.equivalences using
  ( _≃_; is-equiv; is-equiv-has-inverse)
open import foundation.functions using (_∘_; id)
open import foundation.homotopies using (_~_)
open import foundation.identity-types using (refl)
open import foundation.universe-levels using (Level; UU)
```

## Idea

We prove arithmetical laws involving the booleans

## Laws

### Dependent pairs over booleans are equivalent to coproducts

```agda
module _
  {l : Level} (A : bool → UU l)
  where

  map-Σ-bool-coprod : Σ bool A → A true + A false
  map-Σ-bool-coprod (pair true a) = inl a
  map-Σ-bool-coprod (pair false a) = inr a

  map-inv-Σ-bool-coprod : A true + A false → Σ bool A
  map-inv-Σ-bool-coprod (inl a) = pair true a
  map-inv-Σ-bool-coprod (inr a) = pair false a

  issec-map-inv-Σ-bool-coprod :
    ( map-Σ-bool-coprod ∘ map-inv-Σ-bool-coprod) ~ id
  issec-map-inv-Σ-bool-coprod (inl a) = refl
  issec-map-inv-Σ-bool-coprod (inr a) = refl

  isretr-map-inv-Σ-bool-coprod :
    ( map-inv-Σ-bool-coprod ∘ map-Σ-bool-coprod) ~ id
  isretr-map-inv-Σ-bool-coprod (pair true a) = refl
  isretr-map-inv-Σ-bool-coprod (pair false a) = refl

  is-equiv-map-Σ-bool-coprod : is-equiv map-Σ-bool-coprod
  is-equiv-map-Σ-bool-coprod =
    is-equiv-has-inverse
      map-inv-Σ-bool-coprod
      issec-map-inv-Σ-bool-coprod
      isretr-map-inv-Σ-bool-coprod

  equiv-Σ-bool-coprod : Σ bool A ≃ (A true + A false)
  pr1 equiv-Σ-bool-coprod = map-Σ-bool-coprod
  pr2 equiv-Σ-bool-coprod = is-equiv-map-Σ-bool-coprod

  is-equiv-map-inv-Σ-bool-coprod : is-equiv map-inv-Σ-bool-coprod
  is-equiv-map-inv-Σ-bool-coprod =
    is-equiv-has-inverse
      map-Σ-bool-coprod
      isretr-map-inv-Σ-bool-coprod
      issec-map-inv-Σ-bool-coprod

  inv-equiv-Σ-bool-coprod : (A true + A false) ≃ Σ bool A
  pr1 inv-equiv-Σ-bool-coprod = map-inv-Σ-bool-coprod
  pr2 inv-equiv-Σ-bool-coprod = is-equiv-map-inv-Σ-bool-coprod
```
