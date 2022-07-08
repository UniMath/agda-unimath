---
title: The universal property of maybe
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation.universal-property-maybe where

open import foundation.cartesian-product-types using (_×_)
open import foundation.coproduct-types using (inl; inr)
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.equivalences using
  ( is-equiv; is-equiv-has-inverse; _≃_)
open import foundation.function-extensionality using (eq-htpy)
open import foundation.functions using (_∘_; id)
open import foundation.homotopies using (_~_)
open import foundation.identity-types using (refl)
open import foundation.maybe using
  ( Maybe; unit-Maybe; exception-Maybe)
open import foundation.unit-type using (star)
open import foundation.universe-levels using (Level; UU)
```

## Idea

We combine the universal property of coproducts and the unit type to obtain a universal property of the maybe modality.

```agda
-- The universal property of Maybe

module _
  {l1 l2 : Level} {A : UU l1} {B : Maybe A → UU l2}
  where

  ev-Maybe :
    ((x : Maybe A) → B x) → ((x : A) → B (unit-Maybe x)) × B exception-Maybe
  pr1 (ev-Maybe h) x = h (unit-Maybe x)
  pr2 (ev-Maybe h) = h exception-Maybe
  
  ind-Maybe :
    ((x : A) → B (unit-Maybe x)) × (B exception-Maybe) → (x : Maybe A) → B x
  ind-Maybe (pair h b) (inl x) = h x
  ind-Maybe (pair h b) (inr star) = b

  abstract
    issec-ind-Maybe : (ev-Maybe ∘ ind-Maybe) ~ id
    issec-ind-Maybe (pair h b) = refl

    isretr-ind-Maybe' :
      (h : (x : Maybe A) → B x) → (ind-Maybe (ev-Maybe h)) ~ h
    isretr-ind-Maybe' h (inl x) = refl
    isretr-ind-Maybe' h (inr star) = refl

    isretr-ind-Maybe : (ind-Maybe ∘ ev-Maybe) ~ id
    isretr-ind-Maybe h = eq-htpy (isretr-ind-Maybe' h)

    dependent-universal-property-Maybe :
      is-equiv ev-Maybe
    dependent-universal-property-Maybe =
      is-equiv-has-inverse
        ind-Maybe
        issec-ind-Maybe
        isretr-ind-Maybe

equiv-dependent-universal-property-Maybe :
  {l1 l2 : Level} {A : UU l1} (B : Maybe A → UU l2) →
  ((x : Maybe A) → B x) ≃ (((x : A) → B (unit-Maybe x)) × B exception-Maybe)
pr1 (equiv-dependent-universal-property-Maybe B) = ev-Maybe
pr2 (equiv-dependent-universal-property-Maybe B) =
  dependent-universal-property-Maybe

equiv-universal-property-Maybe :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} → (Maybe A → B) ≃ ((A → B) × B)
equiv-universal-property-Maybe {l1} {l2} {A} {B} =
  equiv-dependent-universal-property-Maybe (λ x → B)
```
