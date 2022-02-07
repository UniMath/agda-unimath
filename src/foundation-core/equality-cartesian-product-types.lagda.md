# Equality of cartesian product types

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation-core.equality-cartesian-product-types where

open import foundation-core.cartesian-product-types using (_×_)
open import foundation-core.dependent-pair-types using (pair; pr1; pr2)
open import foundation-core.equivalences using
  ( is-equiv; _≃_; is-equiv-has-inverse)
open import foundation-core.functions using (id; _∘_)
open import foundation-core.homotopies using (_~_)
open import foundation-core.identity-types using (Id; refl; ap)
open import foundation-core.universe-levels using (UU; Level; _⊔_)
```

## Idea

Identifications `Id (pair x y) (pair x' y')` in a cartesian product are equivalently described as pairs of identifications `Id x x'` and `Id y y'`. This provides us with a characterization of the identity type of cartesian product types.

## Definition

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where
  
  Eq-prod : (s t : A × B) → UU (l1 ⊔ l2)
  Eq-prod s t = (Id (pr1 s) (pr1 t)) × (Id (pr2 s) (pr2 t))
```

## Properties

### The type `Eq-prod s t` is equivalent to `Id s t`.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where
  
  eq-pair' : {s t : A × B} → Eq-prod s t → Id s t
  eq-pair' {pair x y} {pair .x .y} (pair refl refl) = refl

  eq-pair :
    {s t : A × B} → Id (pr1 s) (pr1 t) → Id (pr2 s) (pr2 t) → Id s t
  eq-pair p q = eq-pair' (pair p q)

  pair-eq : {s t : A × B} → Id s t → Eq-prod s t
  pr1 (pair-eq α) = ap pr1 α
  pr2 (pair-eq α) = ap pr2 α

  isretr-pair-eq :
    {s t : A × B} → ((pair-eq {s} {t}) ∘ (eq-pair' {s} {t})) ~ id
  isretr-pair-eq {pair x y} {pair .x .y} (pair refl refl) = refl

  issec-pair-eq :
    {s t : A × B} → ((eq-pair' {s} {t}) ∘ (pair-eq {s} {t})) ~ id
  issec-pair-eq {pair x y} {pair .x .y} refl = refl

  abstract
    is-equiv-eq-pair :
      (s t : A × B) → is-equiv (eq-pair' {s} {t})
    is-equiv-eq-pair s t =
      is-equiv-has-inverse pair-eq issec-pair-eq isretr-pair-eq

  equiv-eq-pair :
    (s t : A × B) → Eq-prod s t ≃ Id s t
  pr1 (equiv-eq-pair s t) = eq-pair'
  pr2 (equiv-eq-pair s t) = is-equiv-eq-pair s t

  abstract
    is-equiv-pair-eq :
      (s t : A × B) → is-equiv (pair-eq {s} {t})
    is-equiv-pair-eq s t =
      is-equiv-has-inverse eq-pair' isretr-pair-eq issec-pair-eq

  equiv-pair-eq :
    (s t : A × B) → Id s t ≃ Eq-prod s t
  pr1 (equiv-pair-eq s t) = pair-eq
  pr2 (equiv-pair-eq s t) = is-equiv-pair-eq s t
```
