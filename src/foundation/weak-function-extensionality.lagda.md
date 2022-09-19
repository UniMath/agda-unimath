---
title: Weak function extensionality
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation.weak-function-extensionality where

open import foundation.1-types using
  ( is-1-type; 1-Type; type-1-Type; is-1-type-type-1-Type)
open import foundation.contractible-types using
  ( is-contr; center; contraction; is-contr-retract-of; is-contr-total-path;
    is-prop-is-contr)
open import foundation.coproduct-types using (inl; inr)
open import foundation.decidable-equality using
  ( has-decidable-equality; is-set-has-decidable-equality)
open import foundation.decidable-types using (is-decidable)
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.empty-types using
  ( is-prop-empty; is-empty; ex-falso)
open import foundation.equality-dependent-pair-types using (eq-pair-Σ)
open import foundation.equivalences using
  ( map-inv-is-equiv; _≃_; is-equiv; is-equiv-has-inverse)
open import foundation.function-extensionality using
  ( FUNEXT; htpy-eq; funext)
open import foundation.functions using (_∘_; id)
open import foundation.fundamental-theorem-of-identity-types using
  ( fundamental-theorem-id)
open import foundation.homotopies using (_~_; refl-htpy)
open import foundation.identity-types using (_＝_; refl; inv; _∙_; ap)
open import foundation.negation using (¬)
open import foundation.propositions using
  ( is-prop; is-prop-equiv; Prop; type-Prop; is-prop-type-Prop; eq-is-prop;
    is-proof-irrelevant-is-prop)
open import foundation.sets using (is-set; Set; type-Set; is-set-type-Set)
open import foundation.subtypes using (is-subtype)
open import foundation.truncated-types using
  ( is-trunc; is-trunc-is-equiv; Truncated-Type; type-Truncated-Type;
    is-trunc-type-Truncated-Type)
open import foundation.truncation-levels using
  ( 𝕋; neg-two-𝕋; neg-one-𝕋; zero-𝕋; one-𝕋; succ-𝕋)
open import foundation.universe-levels using (Level; UU; _⊔_)
```

## Idea

Weak function extensionality is the principle that any dependent product of contractible types is contractible. This principle is equivalent to the function extensionality axiom.

## Definition

### Weak function extensionality

```agda
WEAK-FUNEXT :
  {i j : Level} (A : UU i) (B : A → UU j) → UU (i ⊔ j)
WEAK-FUNEXT A B =
  ((x : A) → is-contr (B x)) → is-contr ((x : A) → B x)
```

### Weaker function extensionality

```agda
WEAKER-FUNEXT :
  {l1 l2 : Level} (A : UU l1) (B : A → UU l2) → UU (l1 ⊔ l2)
WEAKER-FUNEXT A B =
  ((x : A) → is-prop (B x)) → is-prop ((x : A) → B x)
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
    fundamental-theorem-id
      ( is-contr-retract-of
        ( (x : A) → Σ (B x) (λ b → f x ＝ b))
        ( pair
          ( λ t x → pair (pr1 t x) (pr2 t x))
          ( pair (λ t → pair (λ x → pr1 (t x)) (λ x → pr2 (t x)))
          ( λ t → eq-pair-Σ refl refl)))
        ( weak-funext A
          ( λ x → Σ (B x) (λ b → f x ＝ b))
          ( λ x → is-contr-total-path (f x))))
      ( λ g → htpy-eq {g = g})
```

### A partial converse to weak function extensionality

```agda
cases-function-converse-weak-funext :
  {l1 l2 : Level} {I : UU l1} {A : I → UU l2} (d : has-decidable-equality I)
  (H : is-contr ((i : I) → A i)) (i : I) (x : A i)
  (j : I) (e : is-decidable (i ＝ j)) → A j
cases-function-converse-weak-funext d H i x .i (inl refl) = x
cases-function-converse-weak-funext d H i x j (inr f) = center H j

function-converse-weak-funext :
  {l1 l2 : Level} {I : UU l1} {A : I → UU l2} (d : has-decidable-equality I)
  (H : is-contr ((i : I) → A i)) (i : I) (x : A i) (j : I) → A j
function-converse-weak-funext d H i x j =
  cases-function-converse-weak-funext d H i x j (d i j)

cases-eq-function-converse-weak-funext :
  {l1 l2 : Level} {I : UU l1} {A : I → UU l2} (d : has-decidable-equality I)
  (H : is-contr ((i : I) → A i)) (i : I) (x : A i) (e : is-decidable (i ＝ i)) →
  cases-function-converse-weak-funext d H i x i e ＝ x
cases-eq-function-converse-weak-funext d H i x (inl p) =
  ap ( λ t → cases-function-converse-weak-funext d H i x i (inl t))
     ( eq-is-prop (is-set-has-decidable-equality d i i) {p} {refl})
cases-eq-function-converse-weak-funext d H i x (inr f) = ex-falso (f refl)

eq-function-converse-weak-funext :
  {l1 l2 : Level} {I : UU l1} {A : I → UU l2} (d : has-decidable-equality I)
  (H : is-contr ((i : I) → A i)) (i : I) (x : A i) →
  function-converse-weak-funext d H i x i ＝ x
eq-function-converse-weak-funext d H i x =
  cases-eq-function-converse-weak-funext d H i x (d i i)

converse-weak-funext :
  {l1 l2 : Level} {I : UU l1} {A : I → UU l2} →
  has-decidable-equality I → is-contr ((i : I) → A i) → (i : I) → is-contr (A i)
pr1 (converse-weak-funext d (pair x H) i) = x i
pr2 (converse-weak-funext d (pair x H) i) y =
  ( htpy-eq (H (function-converse-weak-funext d (pair x H) i y)) i) ∙
  ( eq-function-converse-weak-funext d (pair x H) i y)
```

### Weaker function extensionality implies weak function extensionality

```agda
weak-funext-weaker-funext :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
  WEAKER-FUNEXT A B → WEAK-FUNEXT A B
weak-funext-weaker-funext H C =
  is-proof-irrelevant-is-prop
    ( H (λ x → is-prop-is-contr (C x)))
    ( λ x → center (C x))
```
