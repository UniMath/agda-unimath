# Retractions

```agda
{-# OPTIONS --safe #-}
```

<details><summary>Imports</summary>
```agda
module foundation-core.retractions where
open import foundation-core.dependent-pair-types
open import foundation-core.functions
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.universe-levels
```
</details>

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
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  where

  retraction-right-factor :
    (g : B → X) (h : A → B) → retr (g ∘ h) → retr h
  pr1 (retraction-right-factor g h retr-gh) = pr1 retr-gh ∘ g
  pr2 (retraction-right-factor g h retr-gh) = pr2 retr-gh

  retraction-right-factor-htpy :
    (f : A → X) (g : B → X) (h : A → B) (H : f ~ (g ∘ h)) → retr f → retr h
  pr1 (retraction-right-factor-htpy f g h H retr-f) =
    pr1 retr-f ∘ g
  pr2 (retraction-right-factor-htpy f g h H retr-f) =
    (inv-htpy ((pr1 retr-f) ·l H)) ∙h (pr2 retr-f)
```

### Composites of retractions are retractions

```agda
  retraction-comp :
    (g : B → X) (h : A → B) → retr g → retr h → retr (g ∘ h)
  pr1 (retraction-comp g h retr-g retr-h) = pr1 retr-h ∘ pr1 retr-g
  pr2 (retraction-comp g h retr-g retr-h) =
    ((pr1 retr-h) ·l (pr2 retr-g ·r h)) ∙h (pr2 retr-h)

  retraction-comp-htpy :
    (f : A → X) (g : B → X) (h : A → B) (H : f ~ (g ∘ h)) →
    retr g → retr h → retr f
  pr1 (retraction-comp-htpy f g h H retr-g retr-h) =
    pr1 (retraction-comp g h retr-g retr-h)
  pr2 (retraction-comp-htpy f g h H retr-g retr-h) =
    ( pr1 (retraction-comp g h retr-g retr-h) ·l H) ∙h
    pr2 (retraction-comp g h retr-g retr-h)

  inv-triangle-retraction :
    (f : A → X) (g : B → X) (h : A → B) (H : f ~ (g ∘ h))
    (retr-g : retr g) → ((pr1 retr-g) ∘ f) ~ h
  inv-triangle-retraction f g h H retr-g = (pr1 retr-g ·l H) ∙h (pr2 retr-g ·r h)

  triangle-retraction :
    (f : A → X) (g : B → X) (h : A → B) (H : f ~ (g ∘ h))
    (retr-g : retr g) → h ~ ((pr1 retr-g) ∘ f)
  triangle-retraction f g h H retr-g = inv-htpy (inv-triangle-retraction f g h H retr-g)
```