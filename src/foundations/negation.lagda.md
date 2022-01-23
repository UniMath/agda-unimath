---
title: Univalent Mathematics in Agda
---

```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module foundations.negation where

open import foundations.cartesian-product-types using (_×_)
open import foundations.coproduct-types using (coprod; inl; inr)
open import foundations.dependent-pair-types using (pr1; pr2; pair)
open import foundations.empty-type using (empty; ex-falso)
open import foundations.functions using (_∘_)
open import foundations.levels using (UU; Level; _⊔_)
```

# Negation

```agda
¬ : {l : Level} → UU l → UU l
¬ A = A → empty

functor-neg : {l1 l2 : Level} {P : UU l1} {Q : UU l2} →
  (P → Q) → (¬ Q → ¬ P)
functor-neg f nq p = nq (f p)
```

## Double negation

```agda
¬¬ : {l : Level} → UU l → UU l
¬¬ P = ¬ (¬ P)

¬¬¬ : {l : Level} → UU l → UU l
¬¬¬ P = ¬ (¬ (¬ P))

intro-dn : {l : Level} {P : UU l} → P → ¬¬ P
intro-dn p f = f p

functor-dn : {l1 l2 : Level} {P : UU l1} {Q : UU l2} →
  (P → Q) → (¬¬ P → ¬¬ Q)
functor-dn f = functor-neg (functor-neg f)

```

```agda
no-fixed-points-neg :
  {l : Level} (A : UU l) → ¬ ((A → ¬ A) × (¬ A → A))
no-fixed-points-neg A (pair f g) =
  ( λ (h : ¬ A) → h (g h)) (λ (a : A) → f a a)
```

```agda
dn-dn-elim : {l : Level} {P : UU l} → ¬¬ (¬¬ P → P)
dn-dn-elim {P = P} f =
  ( λ (np : ¬ P) → f (λ (nnp : ¬¬ P) → ex-falso (nnp np)))
    ( λ (p : P) → f (λ (nnp : ¬¬ P) → p))
```

## Double negations of classical laws

```agda
Peirces-law :
  {l1 l2 : Level} {P : UU l1} {Q : UU l2} →
  ¬¬ (((P → Q) → P) → P)
Peirces-law {P = P} {Q} f =
  ( λ (np : ¬ P) → f (λ h → h (λ p → ex-falso (np p))))
  ( λ (p : P) → f (λ h → p))

dn-linearity-implication :
  {l1 l2 : Level} {P : UU l1} {Q : UU l2} →
  ¬¬ (coprod (P → Q) (Q → P))
dn-linearity-implication {P = P} {Q = Q} f =
  ( λ (np : ¬ P) →
    functor-neg (inl {A = P → Q} {B = Q → P}) f (λ p → ex-falso (np p)))
    ( λ (p : P) →
      functor-neg (inr {A = P → Q} {B = Q → P}) f (λ q → p))
```

## Cases of double negation elimination

```agda
dn-elim-neg : {l : Level} (P : UU l) → ¬¬¬ P → ¬ P
dn-elim-neg P f p = f (λ g → g p)

dn-extend :
  {l1 l2 : Level} {P : UU l1} {Q : UU l2} →
  (P → ¬¬ Q) → (¬¬ P → ¬¬ Q)
dn-extend {P = P} {Q = Q} f = dn-elim-neg (¬ Q) ∘ (functor-dn f)

dn-elim-exp :
  {l1 l2 : Level} {P : UU l1} {Q : UU l2} →
  ¬¬ (P → ¬¬ Q) → (P → ¬¬ Q)
dn-elim-exp {P = P} {Q = Q} f p =
  dn-elim-neg (¬ Q) (functor-dn (λ (g : P → ¬¬ Q) → g p) f)

dn-elim-prod :
  {l1 l2 : Level} {P : UU l1} {Q : UU l2} →
  ¬¬ ((¬¬ P) × (¬¬ Q)) → (¬¬ P) × (¬¬ Q)
pr1 (dn-elim-prod {P = P} {Q = Q} f) = dn-elim-neg (¬ P) (functor-dn pr1 f)
pr2 (dn-elim-prod {P = P} {Q = Q} f) = dn-elim-neg (¬ Q) (functor-dn pr2 f)
```
