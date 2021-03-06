---
title: Equality of dependent pair types
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation.equality-dependent-pair-types where

open import foundation-core.equality-dependent-pair-types public

open import foundation.identity-types using
  (_＝_; refl; tr; _∙_; concat; ap; tr-concat; inv; isretr-inv-tr)
open import foundation-core.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation-core.equivalences using
  ( is-equiv; _≃_; is-equiv-has-inverse)
open import foundation-core.functions using (id; _∘_)
open import foundation-core.homotopies using (_~_)
open import foundation-core.identity-types using
  ( refl; tr; _∙_; concat; ap; tr-concat)
open import foundation-core.propositions using (is-prop; eq-is-prop)
open import foundation-core.universe-levels using (UU; Level; _⊔_)
```

## Properties

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where
  
  comp-eq-pair-Σ :
    {x y z : A} (a : B x) (b : B y) (c : B z) (p : x ＝ y) (q : y ＝ z) →
    ( r : tr B p a ＝ b) (s : tr B q b ＝ c) → 
    ( concat
      {x = pair x a}
      {y = pair y b}
      ( eq-pair-Σ p r)
      ( pair z c)
      ( eq-pair-Σ q s)) ＝
    ( eq-pair-Σ (p ∙ q) (tr-concat {B = B} p q a ∙ (ap (tr B q) r ∙ s)))
  comp-eq-pair-Σ a .a .a refl refl refl refl = refl

  comp-pair-eq-Σ : {s t u : Σ A B} (p : s ＝ t) (q : t ＝ u) →
    (pr1 (pair-eq-Σ p) ∙ pr1 (pair-eq-Σ q)) ＝ pr1 (pair-eq-Σ (p ∙ q))
  comp-pair-eq-Σ refl refl = refl

  ap-pair-eq-Σ : {l3 : Level} (X : UU l3) (f : X → Σ A B)
    (x y : X) (p : x ＝ y) →
    (pr1 (pair-eq-Σ (ap f p))) ＝ (ap (λ x → pr1 (f x)) p)
  ap-pair-eq-Σ X f x .x refl = refl

  inv-eq-pair-Σ : 
    {x y : A} (a : B x) (b : B y) (p : x ＝ y) (r : tr B p a ＝ b) → 
    ( inv (eq-pair-Σ p r)) ＝
    ( eq-pair-Σ
      ( inv p)
      ( tr
        ( λ x → tr B (inv p) b ＝ x)
        ( isretr-inv-tr B p a)
        ( ap (tr B (inv p)) (inv r))))
  inv-eq-pair-Σ a .a refl refl = refl
```
