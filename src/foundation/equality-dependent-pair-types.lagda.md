---
title: Univalent Mathematics in Agda
---

```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module foundation.equality-dependent-pair-types where

open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.equivalences using (is-equiv; _≃_; is-equiv-has-inverse)
open import foundation.functions using (id; _∘_)
open import foundation.homotopies using (_~_)
open import foundation.identity-types using (Id; refl; tr)
open import foundation.universe-levels using (UU; Level; _⊔_)
```

# The identity type of a dependent pair type

In this file we characterize the identity type of a dependent pair type.

```agda

module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  Eq-Σ : (s t : Σ A B) → UU (l1 ⊔ l2)
  Eq-Σ s t = Σ (Id (pr1 s) (pr1 t)) (λ α → Id (tr B α (pr2 s)) (pr2 t))

  refl-Eq-Σ : (s : Σ A B) → Eq-Σ s s
  pr1 (refl-Eq-Σ (pair a b)) = refl
  pr2 (refl-Eq-Σ (pair a b)) = refl

  pair-eq-Σ : {s t : Σ A B} → Id s t → Eq-Σ s t
  pair-eq-Σ {s} refl = refl-Eq-Σ s

  eq-pair-Σ :
    {s t : Σ A B} →
    (α : Id (pr1 s) (pr1 t)) → Id (tr B α (pr2 s)) (pr2 t) → Id s t
  eq-pair-Σ {pair x y} {pair .x .y} refl refl = refl

  eq-pair-Σ' : {s t : Σ A B} → Eq-Σ s t → Id s t
  eq-pair-Σ' (pair α β) = eq-pair-Σ α β

  isretr-pair-eq-Σ :
    (s t : Σ A B) →
    ((pair-eq-Σ {s} {t}) ∘ (eq-pair-Σ' {s} {t})) ~ id {A = Eq-Σ s t}
  isretr-pair-eq-Σ (pair x y) (pair .x .y) (pair refl refl) = refl

  issec-pair-eq-Σ :
    (s t : Σ A B) → ((eq-pair-Σ' {s} {t}) ∘ (pair-eq-Σ {s} {t})) ~ id
  issec-pair-eq-Σ (pair x y) .(pair x y) refl = refl

  abstract
    is-equiv-eq-pair-Σ : (s t : Σ A B) → is-equiv (eq-pair-Σ' {s} {t})
    is-equiv-eq-pair-Σ s t =
      is-equiv-has-inverse
        ( pair-eq-Σ)
        ( issec-pair-eq-Σ s t)
        ( isretr-pair-eq-Σ s t)

  equiv-eq-pair-Σ : (s t : Σ A B) → Eq-Σ s t ≃ Id s t
  equiv-eq-pair-Σ s t = pair eq-pair-Σ' (is-equiv-eq-pair-Σ s t)

  abstract
    is-equiv-pair-eq-Σ : (s t : Σ A B) → is-equiv (pair-eq-Σ {s} {t})
    is-equiv-pair-eq-Σ s t =
      is-equiv-has-inverse
        ( eq-pair-Σ')
        ( isretr-pair-eq-Σ s t)
        ( issec-pair-eq-Σ s t)

  equiv-pair-eq-Σ : (s t : Σ A B) → Id s t ≃ Eq-Σ s t
  equiv-pair-eq-Σ s t = pair pair-eq-Σ (is-equiv-pair-eq-Σ s t)

  η-pair : (t : Σ A B) → Id (pair (pr1 t) (pr2 t)) t
  η-pair t = eq-pair-Σ refl refl
```
