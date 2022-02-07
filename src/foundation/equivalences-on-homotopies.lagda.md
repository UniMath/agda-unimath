# Equivalences on homotopies

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation.equivalences-on-homotopies where

open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.equivalences using
  ( is-equiv; is-equiv-has-inverse; _≃_; is-equiv-id)
open import foundation.function-extensionality using (eq-htpy)
open import foundation.functions using (_∘_; id)
open import foundation.homotopies using
  ( inv-htpy; _~_; concat-htpy; concat-htpy')
open import foundation.homotopy-induction using (ind-htpy)
open import foundation.identity-types using
  ( inv-inv; issec-inv-concat'; isretr-inv-concat')
open import foundation.universe-levels using (Level; UU)
```

## Idea

We show that the groupoidal operations on homotopy are equivalences.

## Properties

```agda
abstract
  is-equiv-inv-htpy :
    {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
    (f g : (x : A) → B x) → is-equiv (inv-htpy {f = f} {g = g})
  is-equiv-inv-htpy f g =
    is-equiv-has-inverse
      ( inv-htpy)
      ( λ H → eq-htpy (λ x → inv-inv (H x)))
      ( λ H → eq-htpy (λ x → inv-inv (H x)))

equiv-inv-htpy :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  (f g : (x : A) → B x) → (f ~ g) ≃ (g ~ f)
pr1 (equiv-inv-htpy f g) = inv-htpy
pr2 (equiv-inv-htpy f g) = is-equiv-inv-htpy f g

abstract
  is-equiv-concat-htpy :
    {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
    {f g : (x : A) → B x} (H : f ~ g) →
    (h : (x : A) → B x) → is-equiv (concat-htpy H h)
  is-equiv-concat-htpy {A = A} {B = B} {f} =
    ind-htpy f
      ( λ g H → (h : (x : A) → B x) → is-equiv (concat-htpy H h))
      ( λ h → is-equiv-id)

equiv-concat-htpy :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  {f g : (x : A) → B x} (H : f ~ g) (h : (x : A) → B x) →
  (g ~ h) ≃ (f ~ h)
pr1 (equiv-concat-htpy H h) = concat-htpy H h
pr2 (equiv-concat-htpy H h) = is-equiv-concat-htpy H h

inv-concat-htpy' :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  (f : (x : A) → B x) {g h : (x : A) → B x} →
  (g ~ h) → (f ~ h) → (f ~ g)
inv-concat-htpy' f K = concat-htpy' f (inv-htpy K)

issec-inv-concat-htpy' :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  (f : (x : A) → B x) {g h : (x : A) → B x}
  (K : g ~ h) → ((concat-htpy' f K) ∘ (inv-concat-htpy' f K)) ~ id
issec-inv-concat-htpy' f K L =
  eq-htpy (λ x → issec-inv-concat' (f x) (K x) (L x))

isretr-inv-concat-htpy' :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  (f : (x : A) → B x) {g h : (x : A) → B x}
  (K : g ~ h) → ((inv-concat-htpy' f K) ∘ (concat-htpy' f K)) ~ id
isretr-inv-concat-htpy' f K L =
  eq-htpy (λ x → isretr-inv-concat' (f x) (K x) (L x))

is-equiv-concat-htpy' :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  (f : (x : A) → B x) {g h : (x : A) → B x} (K : g ~ h) →
  is-equiv (concat-htpy' f K)
is-equiv-concat-htpy' f K =
  is-equiv-has-inverse
    ( inv-concat-htpy' f K)
    ( issec-inv-concat-htpy' f K)
    ( isretr-inv-concat-htpy' f K)

equiv-concat-htpy' :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  (f : (x : A) → B x) {g h : (x : A) → B x} (K : g ~ h) →
  (f ~ g) ≃ (f ~ h)
pr1 (equiv-concat-htpy' f K) = concat-htpy' f K
pr2 (equiv-concat-htpy' f K) = is-equiv-concat-htpy' f K
```
