---
title: Univalent Mathematics in Agda
---

# Decidable equality

```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module foundation.decidable-equality where

open import foundation.cartesian-product-types using (_×_)
open import foundation.coproduct-types using (inl; inr)
open import foundation.decidable-types using
  ( is-decidable; is-decidable-retract-of; is-decidable-iff; is-decidable-equiv)
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.embeddings using (equiv-ap)
open import foundation.empty-type using (empty)
open import foundation.equivalences using (_≃_; map-equiv; inv-equiv)
open import foundation.identity-types using (Id; refl; ap)
open import foundation.propositions using (is-prop; eq-is-prop)
open import foundation.retractions using (_retract-of_; retract-eq)
open import foundation.unit-type using (unit; star)
open import foundation.universe-levels using (Level; UU; lzero)
```

## Decidable equality

Here we prove only very basic things about decidable equality. Hedberg's theorem, asserting that types with decidable equality are sets, is in `sets`.

```
has-decidable-equality : {l : Level} (A : UU l) → UU l
has-decidable-equality A = (x y : A) → is-decidable (Id x y)

has-decidable-equality-empty : has-decidable-equality empty
has-decidable-equality-empty ()

has-decidable-equality-unit :
  has-decidable-equality unit
has-decidable-equality-unit star star = inl refl

has-decidable-equality-prod' :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  (f : B → has-decidable-equality A) (g : A → has-decidable-equality B) →
  has-decidable-equality (A × B)
has-decidable-equality-prod' f g (pair x y) (pair x' y') with
  f y x x' | g x y y'
... | inl refl | inl refl = inl refl
... | inl refl | inr nq = inr (λ r → nq (ap pr2 r))
... | inr np | inl refl = inr (λ r → np (ap pr1 r))
... | inr np | inr nq = inr (λ r → np (ap pr1 r))

has-decidable-equality-prod :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  has-decidable-equality A → has-decidable-equality B →
  has-decidable-equality (A × B)
has-decidable-equality-prod d e =
  has-decidable-equality-prod' (λ y → d) (λ x → e)

has-decidable-equality-left-factor :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  has-decidable-equality (A × B) → B → has-decidable-equality A
has-decidable-equality-left-factor d b x y with d (pair x b) (pair y b)
... | inl p = inl (ap pr1 p)
... | inr np = inr (λ q → np (ap (λ z → pair z b) q))

has-decidable-equality-right-factor :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  has-decidable-equality (A × B) → A → has-decidable-equality B
has-decidable-equality-right-factor d a x y with d (pair a x) (pair a y)
... | inl p = inl (ap pr2 p)
... | inr np = inr (λ q → np (ap (pair a) q))
```

### Types with decidable equality are closed under retracts

```agda
abstract
  has-decidable-equality-retract-of :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} →
    A retract-of B → has-decidable-equality B → has-decidable-equality A
  has-decidable-equality-retract-of (pair i (pair r H)) d x y =
    is-decidable-retract-of
      ( retract-eq (pair i (pair r H)) x y)
      ( d (i x) (i y))
```

```agda
abstract
  has-decidable-equality-is-prop :
    {l1 : Level} {A : UU l1} → is-prop A → has-decidable-equality A
  has-decidable-equality-is-prop H x y = inl (eq-is-prop H)

abstract
  has-decidable-equality-equiv :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} (e : A ≃ B) →
    has-decidable-equality B → has-decidable-equality A
  has-decidable-equality-equiv e dB x y =
    is-decidable-equiv (equiv-ap e x y) (dB (map-equiv e x) (map-equiv e y))
  
abstract
  has-decidable-equality-equiv' :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} (e : A ≃ B) →
    has-decidable-equality A → has-decidable-equality B
  has-decidable-equality-equiv' e = has-decidable-equality-equiv (inv-equiv e)
```
