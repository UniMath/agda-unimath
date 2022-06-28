# Retractions

```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module foundation-core.retractions where

open import foundation-core.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation-core.functions using (_∘_; id)
open import foundation-core.homotopies using (_~_)
open import foundation-core.identity-types using
  ( _＝_; inv; _∙_; ap; refl; left-inv)
open import foundation-core.universe-levels using (Level; UU; _⊔_)
```

## Idea

A retraction is a map that has a section

## Definition

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where
  
  retr : (f : A → B) → UU (l1 ⊔ l2)
  retr f = Σ (B → A) (λ g → (g ∘ f) ~ id)

_retract-of_ :
  {i j : Level} → UU i → UU j → UU (i ⊔ j)
A retract-of B = Σ (A → B) retr

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where
  
  section-retract-of : A retract-of B → A → B
  section-retract-of = pr1

  retr-section-retract-of : (R : A retract-of B) → retr (section-retract-of R)
  retr-section-retract-of = pr2

  retraction-retract-of : (A retract-of B) → B → A
  retraction-retract-of R = pr1 (retr-section-retract-of R)

  is-retr-retraction-retract-of :
    (R : A retract-of B) →
    (retraction-retract-of R ∘ section-retract-of R) ~ id
  is-retr-retraction-retract-of R = pr2 (retr-section-retract-of R)
```

## Properties

### If A is a retraction of B, then the identity types of A are retractions of the identity types of B

```agda
ap-retraction :
  {i j : Level} {A : UU i} {B : UU j}
  (i : A → B) (r : B → A) (H : (r ∘ i) ~ id)
  (x y : A) → i x ＝ i y → x ＝ y
ap-retraction i r H x y p =
    ( inv (H x)) ∙ ((ap r p) ∙ (H y))

isretr-ap-retraction :
  {i j : Level} {A : UU i} {B : UU j}
  (i : A → B) (r : B → A) (H : (r ∘ i) ~ id)
  (x y : A) → ((ap-retraction i r H x y) ∘ (ap i {x} {y})) ~ id
isretr-ap-retraction i r H x .x refl = left-inv (H x)

retr-ap :
  {i j : Level} {A : UU i} {B : UU j} (i : A → B) →
  retr i → (x y : A) → retr (ap i {x} {y})
pr1 (retr-ap i (pair r H) x y) = ap-retraction i r H x y
pr2 (retr-ap i (pair r H) x y) = isretr-ap-retraction i r H x y

retract-eq :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (R : A retract-of B) →
  (x y : A) → (x ＝ y) retract-of (pr1 R x ＝ pr1 R y)
pr1 (retract-eq (pair i (pair r H)) x y) = ap i
pr2 (retract-eq (pair i (pair r H)) x y) = retr-ap i (pair r H) x y
```
