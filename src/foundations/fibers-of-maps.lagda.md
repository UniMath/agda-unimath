---
title: Univalent Mathematics in Agda
---

```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module foundations.fibers-of-maps where

open import foundations.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundations.equivalences using (is-equiv; is-equiv-has-inverse; _≃_)
open import foundations.functions using (_∘_; id)
open import foundations.homotopies using (_~_)
open import foundations.identity-types using (Id; refl; ap; _∙_)
open import foundations.levels using (Level; UU; _⊔_)
```

# Fibers of maps

We introduce fibers of maps and immediately characterize their identity types.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) (b : B)
  where
  
  fib : UU (l1 ⊔ l2)
  fib = Σ A (λ x → Id (f x) b)

  fib' : UU (l1 ⊔ l2)
  fib' = Σ A (λ x → Id b (f x))

  Eq-fib : fib → fib → UU (l1 ⊔ l2)
  Eq-fib s t = Σ (Id (pr1 s) (pr1 t)) (λ α → Id ((ap f α) ∙ (pr2 t)) (pr2 s))

  {- Proposition 10.3.3 -}
  
  refl-Eq-fib : (s : fib) → Eq-fib s s
  pr1 (refl-Eq-fib s) = refl
  pr2 (refl-Eq-fib s) = refl

  Eq-eq-fib : {s t : fib} → Id s t → Eq-fib s t
  Eq-eq-fib {s} refl = refl-Eq-fib s

  eq-Eq-fib' : {s t : fib} → Eq-fib s t → Id s t
  eq-Eq-fib' {pair x p} {pair .x .p} (pair refl refl) = refl

  eq-Eq-fib :
    {s t : fib} (α : Id (pr1 s) (pr1 t)) →
    Id ((ap f α) ∙ (pr2 t)) (pr2 s) → Id s t
  eq-Eq-fib α β = eq-Eq-fib' (pair α β)

  issec-eq-Eq-fib : {s t : fib} → (Eq-eq-fib {s} {t} ∘ eq-Eq-fib' {s} {t}) ~ id
  issec-eq-Eq-fib {pair x p} {pair .x .p} (pair refl refl) = refl

  isretr-eq-Eq-fib : {s t : fib} → (eq-Eq-fib' {s} {t} ∘ Eq-eq-fib {s} {t}) ~ id
  isretr-eq-Eq-fib {pair x p} {.(pair x p)} refl = refl

  abstract
    is-equiv-Eq-eq-fib : {s t : fib} → is-equiv (Eq-eq-fib {s} {t})
    is-equiv-Eq-eq-fib {s} {t} =
      is-equiv-has-inverse
        eq-Eq-fib'
        issec-eq-Eq-fib
        isretr-eq-Eq-fib

  equiv-Eq-eq-fib : {s t : fib} → Id s t ≃ Eq-fib s t
  pr1 (equiv-Eq-eq-fib {s} {t}) = Eq-eq-fib
  pr2 (equiv-Eq-eq-fib {s} {t}) = is-equiv-Eq-eq-fib

  abstract
    is-equiv-eq-Eq-fib :
      {s t : fib} → is-equiv (eq-Eq-fib' {s} {t})
    is-equiv-eq-Eq-fib {s} {t} =
      is-equiv-has-inverse
        Eq-eq-fib
        isretr-eq-Eq-fib
        issec-eq-Eq-fib

  equiv-eq-Eq-fib : {s t : fib} → Eq-fib s t ≃ Id s t
  pr1 (equiv-eq-Eq-fib {s} {t}) = eq-Eq-fib'
  pr2 (equiv-eq-Eq-fib {s} {t}) = is-equiv-eq-Eq-fib
```
