---
title: Univalent Mathematics in Agda
---

```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module foundations.decidable-types where

open import foundations.cartesian-product-types using (_×_)
open import foundations.coproduct-types using (coprod; inl; inr; ind-coprod)
open import foundations.dependent-pair-types using (pair; pr1; pr2)
open import foundations.double-negation using (¬¬)
open import foundations.empty-type using (empty; ex-falso)
open import foundations.functions using (id; _∘_)
open import foundations.levels using (UU; Level; _⊔_)
open import foundations.negation using (¬; functor-neg)
open import foundations.unit-type using (unit; star)
```

# Decidable types

```agda
is-decidable : {l : Level} (A : UU l) → UU l
is-decidable A = coprod A (¬ A)

is-decidable-fam :
  {l1 l2 : Level} {A : UU l1} (P : A → UU l2) → UU (l1 ⊔ l2)
is-decidable-fam {A = A} P = (x : A) → is-decidable (P x)
```

## Examples of decidable types

```
is-decidable-unit : is-decidable unit
is-decidable-unit = inl star

is-decidable-empty : is-decidable empty
is-decidable-empty = inr id

is-decidable-coprod :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  is-decidable A → is-decidable B → is-decidable (coprod A B)
is-decidable-coprod (inl a) y = inl (inl a)
is-decidable-coprod (inr na) (inl b) = inl (inr b)
is-decidable-coprod (inr na) (inr nb) = inr (ind-coprod (λ x → empty) na nb)

is-decidable-prod :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  is-decidable A → is-decidable B → is-decidable (A × B)
is-decidable-prod (inl a) (inl b) = inl (pair a b)
is-decidable-prod (inl a) (inr g) = inr (g ∘ pr2)
is-decidable-prod (inr f) (inl b) = inr (f ∘ pr1)
is-decidable-prod (inr f) (inr g) = inr (f ∘ pr1)

is-decidable-prod' :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  is-decidable A → (A → is-decidable B) → is-decidable (A × B)
is-decidable-prod' (inl a) d with d a
... | inl b = inl (pair a b)
... | inr nb = inr (nb ∘ pr2)
is-decidable-prod' (inr na) d = inr (na ∘ pr1)

is-decidable-function-type :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  is-decidable A → is-decidable B → is-decidable (A → B)
is-decidable-function-type (inl a) (inl b) = inl (λ x → b)
is-decidable-function-type (inl a) (inr g) = inr (λ h → g (h a))
is-decidable-function-type (inr f) (inl b) = inl (ex-falso ∘ f)
is-decidable-function-type (inr f) (inr g) = inl (ex-falso ∘ f)

is-decidable-function-type' :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  is-decidable A → (A → is-decidable B) → is-decidable (A → B)
is-decidable-function-type' (inl a) d with d a
... | inl b = inl (λ x → b)
... | inr nb = inr (λ f → nb (f a))
is-decidable-function-type' (inr na) d = inl (ex-falso ∘ na)

is-decidable-neg :
  {l : Level} {A : UU l} → is-decidable A → is-decidable (¬ A)
is-decidable-neg d = is-decidable-function-type d is-decidable-empty
```

## Decidability implies double negation elimination

```
dn-elim-is-decidable :
  {l : Level} (P : UU l) → is-decidable P → (¬¬ P → P)
dn-elim-is-decidable P (inl x) p = x
dn-elim-is-decidable P (inr x) p = ex-falso (p x)

dn-is-decidable : {l : Level} {P : UU l} → ¬¬ (is-decidable P)
dn-is-decidable {P = P} f =
  functor-neg (inr {A = P} {B = ¬ P}) f
    ( functor-neg (inl {A = P} {B = ¬ P}) f)

is-decidable-iff :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  (A → B) → (B → A) → is-decidable A → is-decidable B
is-decidable-iff f g (inl a) = inl (f a)
is-decidable-iff f g (inr na) = inr (λ b → na (g b))

idempotent-is-decidable :
  {l : Level} (P : UU l) → is-decidable (is-decidable P) → is-decidable P
idempotent-is-decidable P (inl (inl p)) = inl p
idempotent-is-decidable P (inl (inr np)) = inr np
idempotent-is-decidable P (inr np) = inr (λ p → np (inl p))
```
