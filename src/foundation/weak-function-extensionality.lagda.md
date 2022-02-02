# Weak function extensionality

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation.weak-function-extensionality where

open import foundation.1-types using
  ( is-1-type; UU-1-Type; type-1-Type; is-1-type-type-1-Type)
open import foundation.contractible-types using
  ( is-contr; center; contraction; is-contr-retract-of; is-contr-total-path)
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.empty-types using
  ( is-prop-empty; is-empty)
open import foundation.equality-dependent-pair-types using (eq-pair-Σ)
open import foundation.equivalences using
  ( map-inv-is-equiv; _≃_; is-equiv; is-equiv-has-inverse)
open import foundation.function-extensionality using
  ( FUNEXT; htpy-eq; funext)
open import foundation.functions using (_∘_; id)
open import foundation.fundamental-theorem-of-identity-types using
  ( fundamental-theorem-id)
open import foundation.homotopies using (_~_; refl-htpy)
open import foundation.identity-types using (Id; refl; inv; _∙_)
open import foundation.negation using (¬)
open import foundation.propositions using
  ( is-prop; is-prop-equiv; UU-Prop; type-Prop; is-prop-type-Prop)
open import foundation.sets using (is-set; UU-Set; type-Set; is-set-type-Set)
open import foundation.subtypes using (is-subtype)
open import foundation.truncated-types using
  ( is-trunc; is-trunc-is-equiv; UU-Truncated-Type; type-Truncated-Type;
    is-trunc-type-Truncated-Type)
open import foundation.truncation-levels using
  ( 𝕋; neg-two-𝕋; neg-one-𝕋; zero-𝕋; one-𝕋; succ-𝕋)
open import foundation.universe-levels using (Level; UU; _⊔_)
```

## Idea

Weak function extensionality is the principle that any dependent product of contractible types is contractible. This principle is equivalent to the function extensionality axiom.

## Definition

```agda
WEAK-FUNEXT :
  {i j : Level} (A : UU i) (B : A → UU j) → UU (i ⊔ j)
WEAK-FUNEXT A B =
  ((x : A) → is-contr (B x)) → is-contr ((x : A) → B x)
```

## Properties

### Weak function extensionality is logically equivalent to function extensionality

```agda
abstract
  WEAK-FUNEXT-FUNEXT :
    {l1 l2 : Level} →
    ((A : UU l1) (B : A → UU l2) (f : (x : A) → B x) → FUNEXT f) →
    ((A : UU l1) (B : A → UU l2) → WEAK-FUNEXT A B)
  pr1 (WEAK-FUNEXT-FUNEXT funext A B is-contr-B) x = center (is-contr-B x)
  pr2 (WEAK-FUNEXT-FUNEXT funext A B is-contr-B) f =
    map-inv-is-equiv (funext A B c f) (λ x → contraction (is-contr-B x) (f x))
    where
    c : (x : A) → B x
    c x = center (is-contr-B x)

abstract
  FUNEXT-WEAK-FUNEXT :
    {l1 l2 : Level} →
    ((A : UU l1) (B : A → UU l2) → WEAK-FUNEXT A B) →
    ((A : UU l1) (B : A → UU l2) (f : (x : A) → B x) → FUNEXT f)
  FUNEXT-WEAK-FUNEXT weak-funext A B f =
    fundamental-theorem-id f
      ( refl-htpy)
      ( is-contr-retract-of
        ( (x : A) → Σ (B x) (λ b → Id (f x) b))
        ( pair
          ( λ t x → pair (pr1 t x) (pr2 t x))
          ( pair (λ t → pair (λ x → pr1 (t x)) (λ x → pr2 (t x)))
          ( λ t → eq-pair-Σ refl refl)))
        ( weak-funext A
          ( λ x → Σ (B x) (λ b → Id (f x) b))
          ( λ x → is-contr-total-path (f x))))
      ( λ g → htpy-eq {g = g})
```
