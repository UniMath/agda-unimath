---
title: Retractions
---

```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module foundation-core.retractions where

open import foundation-core.dependent-pair-types
open import foundation-core.functions using (_∘_; id)
open import foundation-core.homotopies
open import foundation-core.identity-types using
  ( _＝_; inv; _∙_; ap; refl; left-inv)
open import foundation-core.universe-levels
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

### If `g ∘ f` has a retraction then `f` has a retraction

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  where

  retraction-right-factor :
    (f : A → B) (g : B → C) → retr (g ∘ f) → retr f
  pr1 (retraction-right-factor f g retr-gf) = pr1 retr-gf ∘ g
  pr2 (retraction-right-factor f g retr-gf) = pr2 retr-gf
  
  retraction-right-factor-htpy :
    (f : A → B) (g : B → C) (h : A → C) (H : h ~ (g ∘ f)) → retr h → retr f
  pr1 (retraction-right-factor-htpy f g h H retr-h) =
    pr1 retr-h ∘ g
  pr2 (retraction-right-factor-htpy f g h H retr-h) = 
    (inv-htpy ((pr1 retr-h) ·l H)) ∙h (pr2 retr-h)
```

### Composites of retractions are retractions

```agda
  retraction-comp : 
    (f : A → B) (g : B → C) → retr f → retr g → retr (g ∘ f)
  pr1 (retraction-comp f g retr-f retr-g) = pr1 retr-f ∘ pr1 retr-g
  pr2 (retraction-comp f g retr-f retr-g) =
    ((pr1 retr-f) ·l (pr2 retr-g ·r f)) ∙h (pr2 retr-f)

  retraction-comp-htpy : 
    (f : A → B) (g : B → C) (h : A → C) (H : h ~ (g ∘ f)) →
    retr f → retr g → retr h
  pr1 (retraction-comp-htpy f g h H retr-f retr-g) =
    pr1 (retraction-comp f g retr-f retr-g)
  pr2 (retraction-comp-htpy f g h H retr-f retr-g) =
    ( pr1 (retraction-comp f g retr-f retr-g) ·l H) ∙h
    pr2 (retraction-comp f g retr-f retr-g)
  

  inv-triangle-retraction :
    (h : A → B) (g : B → C) (f : A → C) (H : f ~ (g ∘ h))
    (retr-g : retr g) → ((pr1 retr-g) ∘ f) ~ h 
  inv-triangle-retraction h g f H retr-g = (pr1 retr-g ·l H) ∙h (pr2 retr-g ·r h)

  triangle-retraction :
    (h : A → B) (g : B → C) (f : A → C) (H : f ~ (g ∘ h))
    (retr-g : retr g) → h ~ ((pr1 retr-g) ∘ f)
  triangle-retraction h g f H retr-g = inv-htpy (inv-triangle-retraction h g f H retr-g)
``` 