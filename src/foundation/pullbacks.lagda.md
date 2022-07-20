---
title: Pullbacks
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation.pullbacks where

open import foundation-core.pullbacks public

open import foundation.contractible-types using
  ( is-contr; is-contr-total-path; is-contr-equiv')
open import foundation.constant-maps using (const)
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2; triple)
open import foundation.diagonal-maps-of-types using (diagonal)
open import foundation.equality-dependent-pair-types using (eq-pair-Σ)
open import foundation.functions using (_∘_; id)
open import foundation.homotopies using (_~_; refl-htpy; right-unit-htpy)
open import foundation.identity-types using
  ( _＝_; refl; ap; _∙_; inv; right-unit; equiv-concat'; equiv-inv)
open import foundation.structure-identity-principle using (extensionality-Σ)
open import foundation.type-theoretic-principle-of-choice using
  ( map-distributive-Π-Σ; mapping-into-Σ; is-equiv-mapping-into-Σ;
    is-equiv-map-distributive-Π-Σ)
open import foundation.unit-type using (unit; star)
open import foundation.universe-levels using (Level; UU; _⊔_)

open import foundation-core.cartesian-product-types using (_×_)
open import foundation-core.cones-pullbacks
open import foundation-core.equivalences using
  ( is-equiv-comp; _∘e_; is-equiv; map-inv-is-equiv; _≃_; id-equiv;
    map-inv-equiv; is-equiv-has-inverse)
open import foundation-core.functoriality-dependent-pair-types using
  ( tot; is-equiv-tot-is-fiberwise-equiv; equiv-tot)
open import foundation-core.universal-property-pullbacks using
  ( universal-property-pullback;
    is-equiv-up-pullback-up-pullback; up-pullback-up-pullback-is-equiv)
```

## Idea

We construct canonical pullbacks of cospans

## Properties

### We characterize the identity type of the canonical pullback

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3} (f : A → X) (g : B → X)
  where

  Eq-canonical-pullback : (t t' : canonical-pullback f g) → UU (l1 ⊔ (l2 ⊔ l3))
  Eq-canonical-pullback (pair a bp) t' =
    let b = pr1 bp
        p = pr2 bp
        a' = pr1 t'
        b' = pr1 (pr2 t')
        p' = pr2 (pr2 t')
    in
    Σ (a ＝ a') (λ α → Σ (b ＝ b') (λ β → ((ap f α) ∙ p') ＝ (p ∙ (ap g β))))

  refl-Eq-canonical-pullback :
    (t : canonical-pullback f g) → Eq-canonical-pullback t t
  pr1 (refl-Eq-canonical-pullback (pair a (pair b p))) = refl
  pr1 (pr2 (refl-Eq-canonical-pullback (pair a (pair b p)))) = refl
  pr2 (pr2 (refl-Eq-canonical-pullback (pair a (pair b p)))) = inv right-unit

  Eq-eq-canonical-pullback :
    (s t : canonical-pullback f g) → s ＝ t → Eq-canonical-pullback s t
  Eq-eq-canonical-pullback s .s refl = refl-Eq-canonical-pullback s

  extensionality-canonical-pullback :
    (t t' : canonical-pullback f g) → (t ＝ t') ≃ Eq-canonical-pullback t t'
  extensionality-canonical-pullback (pair a (pair b p)) =
    extensionality-Σ
      ( λ {a'} bp' α →
        Σ (b ＝ pr1 bp') (λ β → (ap f α ∙ pr2 bp') ＝ (p ∙ ap g β)))
      ( refl)
      ( pair refl (inv right-unit))
      ( λ x → id-equiv)
      ( extensionality-Σ
        ( λ {b'} p' β → p' ＝ (p ∙ ap g β))
        ( refl)
        ( inv right-unit)
        ( λ y → id-equiv)
        ( λ p' → equiv-concat' p' (inv right-unit) ∘e equiv-inv p p'))

  map-extensionality-canonical-pullback :
    { s t : canonical-pullback f g} →
    ( α : pr1 s ＝ pr1 t) (β : pr1 (pr2 s) ＝ pr1 (pr2 t)) →
    ( ((ap f α) ∙ (pr2 (pr2 t))) ＝ ((pr2 (pr2 s)) ∙ (ap g β))) → s ＝ t
  map-extensionality-canonical-pullback {s} {t} α β γ =
    map-inv-equiv
      ( extensionality-canonical-pullback s t)
      ( triple α β γ)
```

### Identity types can be presented as pullbacks

```agda
cone-Id :
  {l : Level} {A : UU l} (x y : A) →
  cone (const unit A x) (const unit A y) (x ＝ y)
cone-Id x y =
  triple (const (x ＝ y) unit star) (const (x ＝ y) unit star) id

inv-gap-cone-Id :
  {l : Level} {A : UU l} (x y : A) →
  canonical-pullback (const unit A x) (const unit A y) → x ＝ y
inv-gap-cone-Id x y (pair star (pair star p)) = p

abstract
  issec-inv-gap-cone-Id :
    {l : Level} {A : UU l} (x y : A) →
    ( ( gap (const unit A x) (const unit A y) (cone-Id x y)) ∘
      ( inv-gap-cone-Id x y)) ~ id
  issec-inv-gap-cone-Id x y (pair star (pair star p)) = refl

abstract
  isretr-inv-gap-cone-Id :
    {l : Level} {A : UU l} (x y : A) →
    ( ( inv-gap-cone-Id x y) ∘
      ( gap (const unit A x) (const unit A y) (cone-Id x y))) ~ id
  isretr-inv-gap-cone-Id x y p = refl

abstract
  is-pullback-cone-Id :
    {l : Level} {A : UU l} (x y : A) →
    is-pullback (const unit A x) (const unit A y) (cone-Id x y)
  is-pullback-cone-Id x y =
    is-equiv-has-inverse
      ( inv-gap-cone-Id x y)
      ( issec-inv-gap-cone-Id x y)
      ( isretr-inv-gap-cone-Id x y)

{- One way to solve this exercise is to show that Id (pr1 t) (pr2 t) is a
   pullback for every t : A × A. This allows one to use path induction to
   show that the inverse of the gap map is a section.
-}

cone-Id' :
  {l : Level} {A : UU l} (t : A × A) →
  cone (const unit (A × A) t) (diagonal A) (pr1 t ＝ pr2 t)
cone-Id' {A = A} (pair x y) =
  triple
    ( const (x ＝ y) unit star)
    ( const (x ＝ y) A x)
    ( λ p → eq-pair-Σ refl (inv p))

inv-gap-cone-Id' :
  {l : Level} {A : UU l} (t : A × A) →
  canonical-pullback (const unit (A × A) t) (diagonal A) → (pr1 t ＝ pr2 t)
inv-gap-cone-Id' t (pair star (pair z p)) =
  (ap pr1 p) ∙ (inv (ap pr2 p))

abstract
  issec-inv-gap-cone-Id' :
    {l : Level} {A : UU l} (t : A × A) →
    ( ( gap (const unit (A × A) t) (diagonal A) (cone-Id' t)) ∘
      ( inv-gap-cone-Id' t)) ~ id
  issec-inv-gap-cone-Id' .(pair z z) (pair star (pair z refl)) = refl

abstract
  isretr-inv-gap-cone-Id' :
    {l : Level} {A : UU l} (t : A × A) →
    ( ( inv-gap-cone-Id' t) ∘
      ( gap (const unit (A × A) t) (diagonal A) (cone-Id' t))) ~ id
  isretr-inv-gap-cone-Id' (pair x .x) refl = refl

abstract
  is-pullback-cone-Id' :
    {l : Level} {A : UU l} (t : A × A) →
    is-pullback (const unit (A × A) t) (diagonal A) (cone-Id' t)
  is-pullback-cone-Id' t =
    is-equiv-has-inverse
      ( inv-gap-cone-Id' t)
      ( issec-inv-gap-cone-Id' t)
      ( isretr-inv-gap-cone-Id' t)
```
