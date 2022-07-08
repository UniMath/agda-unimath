---
title: The universal property of the natural numbers
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module elementary-number-theory.universal-property-natural-numbers where

open import elementary-number-theory.natural-numbers using (ℕ; zero-ℕ; succ-ℕ)

open import foundation.cartesian-product-types using (_×_)
open import foundation.contractible-types using (is-contr; is-contr-total-path)
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2; triple)
open import foundation.equivalences using
  ( is-equiv; map-inv-is-equiv; _≃_; _∘e_; id-equiv)
open import foundation.function-extensionality using (equiv-funext)
open import foundation.functions using (_∘_)
open import foundation.functoriality-cartesian-product-types using
  ( equiv-prod)
open import foundation.fundamental-theorem-of-identity-types using
  ( fundamental-theorem-id)
open import foundation.homotopies using (_~_; refl-htpy; is-contr-total-htpy)
open import foundation.identity-types using
  ( _＝_; _∙_; ap; refl; right-unit; inv; left-inv; assoc)
open import foundation.structure-identity-principle using
  ( is-contr-total-Eq-structure)
open import foundation.universe-levels using (Level; UU)
```

## Idea

The universal property of the natural numbers asserts that for any type `X` equipped with a point `x : X` and an endomorphism `f : X → X`, the type of structure preserving maps from `ℕ` to `X` is contractible.

```agda
module _
  {l : Level} {X : UU l} (x : X) (f : X → X)
  where

  structure-preserving-map-ℕ : UU l
  structure-preserving-map-ℕ =
    Σ (ℕ → X) (λ h → (h zero-ℕ ＝ x) × ((h ∘ succ-ℕ) ~ (f ∘ h)))

  htpy-structure-preserving-map-ℕ :
    (h k : structure-preserving-map-ℕ) → UU l
  htpy-structure-preserving-map-ℕ h k =
    Σ ( pr1 h ~ pr1 k)
      ( λ H →
        ( pr1 (pr2 h) ＝ (H zero-ℕ ∙ pr1 (pr2 k))) ×
        ( (n : ℕ) →
          (pr2 (pr2 h) n ∙ ap f (H n)) ＝ (H (succ-ℕ n) ∙ pr2 (pr2 k) n)))

  refl-htpy-structure-preserving-map-ℕ :
    (h : structure-preserving-map-ℕ) → htpy-structure-preserving-map-ℕ h h
  refl-htpy-structure-preserving-map-ℕ h =
    triple refl-htpy refl (λ n → right-unit)

  htpy-eq-structure-preserving-map-ℕ :
    {h k : structure-preserving-map-ℕ} → h ＝ k →
    htpy-structure-preserving-map-ℕ h k
  htpy-eq-structure-preserving-map-ℕ {h} refl =
    refl-htpy-structure-preserving-map-ℕ h

  is-contr-total-htpy-structure-preserving-map-ℕ :
    (h : structure-preserving-map-ℕ) →
    is-contr (Σ structure-preserving-map-ℕ (htpy-structure-preserving-map-ℕ h))
  is-contr-total-htpy-structure-preserving-map-ℕ h =
    is-contr-total-Eq-structure
      ( λ g p (H : pr1 h ~ g) →
        ( pr1 (pr2 h) ＝ (H zero-ℕ ∙ pr1 p)) ×
        ( (n : ℕ) →
          (pr2 (pr2 h) n ∙ ap f (H n)) ＝ (H (succ-ℕ n) ∙ pr2 p n)))
      ( is-contr-total-htpy (pr1 h))
      ( pair (pr1 h) refl-htpy)
      ( is-contr-total-Eq-structure
        ( λ p0 pS q →
          (n : ℕ) → (pr2 (pr2 h) n ∙ refl) ＝ pS n)
        ( is-contr-total-path (pr1 (pr2 h)))
        ( pair (pr1 (pr2 h)) refl)
        ( is-contr-total-htpy (λ n → (pr2 (pr2 h) n ∙ refl))))

  is-equiv-htpy-eq-structure-preserving-map-ℕ :
    (h k : structure-preserving-map-ℕ) →
    is-equiv (htpy-eq-structure-preserving-map-ℕ {h} {k})
  is-equiv-htpy-eq-structure-preserving-map-ℕ h =
    fundamental-theorem-id h
      ( refl-htpy-structure-preserving-map-ℕ h)
      ( is-contr-total-htpy-structure-preserving-map-ℕ h)
      ( λ k → htpy-eq-structure-preserving-map-ℕ {h} {k})

  eq-htpy-structure-preserving-map-ℕ :
    {h k : structure-preserving-map-ℕ} →
    htpy-structure-preserving-map-ℕ h k → h ＝ k
  eq-htpy-structure-preserving-map-ℕ {h} {k} =
    map-inv-is-equiv (is-equiv-htpy-eq-structure-preserving-map-ℕ h k)

  center-structure-preserving-map-ℕ : structure-preserving-map-ℕ
  center-structure-preserving-map-ℕ = triple h p H
    where
    h : ℕ → X
    h zero-ℕ = x
    h (succ-ℕ n) = f (h n)
    p : h zero-ℕ ＝ x
    p = refl
    H : (h ∘ succ-ℕ) ~ (f ∘ h)
    H = refl-htpy

  contraction-structure-preserving-map-ℕ :
    (h : structure-preserving-map-ℕ) → center-structure-preserving-map-ℕ ＝ h
  contraction-structure-preserving-map-ℕ h =
    eq-htpy-structure-preserving-map-ℕ (triple α β γ)
    where
    α : pr1 center-structure-preserving-map-ℕ ~ pr1 h
    α zero-ℕ = inv (pr1 (pr2 h))
    α (succ-ℕ n) = ap f (α n) ∙ inv (pr2 (pr2 h) n)
    β : pr1 (pr2 center-structure-preserving-map-ℕ) ＝ (α zero-ℕ ∙ pr1 (pr2 h))
    β = inv (left-inv (pr1 (pr2 h)))
    γ : (n : ℕ) →
        ( pr2 (pr2 center-structure-preserving-map-ℕ) n ∙ ap f (α n)) ＝
        ( α (succ-ℕ n) ∙ pr2 (pr2 h) n)
    γ n = ( ( inv right-unit) ∙
            ( ap (λ q → (ap f (α n) ∙ q)) (inv (left-inv (pr2 (pr2 h) n))))) ∙
          ( inv (assoc (ap f (α n)) (inv (pr2 (pr2 h) n)) (pr2 (pr2 h) n)))

  is-contr-structure-preserving-map-ℕ : is-contr structure-preserving-map-ℕ
  pr1 is-contr-structure-preserving-map-ℕ = center-structure-preserving-map-ℕ
  pr2 is-contr-structure-preserving-map-ℕ =
    contraction-structure-preserving-map-ℕ
```
