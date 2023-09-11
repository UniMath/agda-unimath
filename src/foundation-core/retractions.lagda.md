# Retractions

```agda
module foundation-core.retractions where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.whiskering-homotopies
```

</details>

## Idea

A **retraction** is a map that has a right inverse, i.e. a section. Thus,
`r : B → A` is a retraction of `f : A → B` if the composition `r ∘ f` is
homotopic to the identity at `A`. Moreover, in this case we say that `A` _is a
retract of_ `B`.

## Definition

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  retraction : (f : A → B) → UU (l1 ⊔ l2)
  retraction f = Σ (B → A) (λ r → (r ∘ f) ~ id)

  map-retraction : (f : A → B) → retraction f → B → A
  map-retraction f = pr1

  is-retraction-map-retraction :
    (f : A → B) (r : retraction f) → (map-retraction f r ∘ f) ~ id
  is-retraction-map-retraction f = pr2

_retract-of_ :
  {l1 l2 : Level} → UU l1 → UU l2 → UU (l1 ⊔ l2)
A retract-of B = Σ (A → B) retraction

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  section-retract-of : A retract-of B → A → B
  section-retract-of = pr1

  retraction-section-retract-of :
    (R : A retract-of B) → retraction (section-retract-of R)
  retraction-section-retract-of = pr2

  retraction-retract-of : (A retract-of B) → B → A
  retraction-retract-of R = pr1 (retraction-section-retract-of R)

  is-retraction-retraction-retract-of :
    (R : A retract-of B) →
    (retraction-retract-of R ∘ section-retract-of R) ~ id
  is-retraction-retraction-retract-of R = pr2 (retraction-section-retract-of R)
```

## Properties

### If `A` is a retraction of `B`, then the identity types of `A` are retractions of the identity types of `B`

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  ap-retraction :
    (i : A → B) (r : B → A) (H : (r ∘ i) ~ id)
    (x y : A) → i x ＝ i y → x ＝ y
  ap-retraction i r H x y p =
      ( inv (H x)) ∙ ((ap r p) ∙ (H y))

  is-retraction-ap-retraction :
    (i : A → B) (r : B → A) (H : (r ∘ i) ~ id)
    (x y : A) → ((ap-retraction i r H x y) ∘ (ap i {x} {y})) ~ id
  is-retraction-ap-retraction i r H x .x refl = left-inv (H x)

  retraction-ap :
    (i : A → B) → retraction i → (x y : A) → retraction (ap i {x} {y})
  pr1 (retraction-ap i (pair r H) x y) = ap-retraction i r H x y
  pr2 (retraction-ap i (pair r H) x y) = is-retraction-ap-retraction i r H x y

  retract-eq :
    (R : A retract-of B) → (x y : A) → (x ＝ y) retract-of (pr1 R x ＝ pr1 R y)
  pr1 (retract-eq (pair i (pair r H)) x y) = ap i
  pr2 (retract-eq (pair i (pair r H)) x y) = retraction-ap i (pair r H) x y
```

### If `g ∘ f` has a retraction then `f` has a retraction

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  where

  retraction-right-factor :
    (g : B → X) (h : A → B) → retraction (g ∘ h) → retraction h
  pr1 (retraction-right-factor g h retraction-gh) = pr1 retraction-gh ∘ g
  pr2 (retraction-right-factor g h retraction-gh) = pr2 retraction-gh

  retraction-right-factor-htpy :
    (f : A → X) (g : B → X) (h : A → B) (H : f ~ (g ∘ h)) →
    retraction f → retraction h
  pr1 (retraction-right-factor-htpy f g h H retraction-f) =
    pr1 retraction-f ∘ g
  pr2 (retraction-right-factor-htpy f g h H retraction-f) =
    (inv-htpy ((pr1 retraction-f) ·l H)) ∙h (pr2 retraction-f)
```

### Composites of retractions are retractions

```agda
  retraction-comp :
    (g : B → X) (h : A → B) → retraction g → retraction h → retraction (g ∘ h)
  pr1 (retraction-comp g h retraction-g retraction-h) =
    pr1 retraction-h ∘ pr1 retraction-g
  pr2 (retraction-comp g h retraction-g retraction-h) =
    ((pr1 retraction-h) ·l (pr2 retraction-g ·r h)) ∙h (pr2 retraction-h)

  retraction-comp-htpy :
    (f : A → X) (g : B → X) (h : A → B) (H : f ~ (g ∘ h)) →
    retraction g → retraction h → retraction f
  pr1 (retraction-comp-htpy f g h H retraction-g retraction-h) =
    pr1 (retraction-comp g h retraction-g retraction-h)
  pr2 (retraction-comp-htpy f g h H retraction-g retraction-h) =
    ( pr1 (retraction-comp g h retraction-g retraction-h) ·l H) ∙h
    pr2 (retraction-comp g h retraction-g retraction-h)

  inv-triangle-retraction :
    (f : A → X) (g : B → X) (h : A → B) (H : f ~ (g ∘ h))
    (retraction-g : retraction g) → ((pr1 retraction-g) ∘ f) ~ h
  inv-triangle-retraction f g h H retraction-g =
    (pr1 retraction-g ·l H) ∙h (pr2 retraction-g ·r h)

  triangle-retraction :
    (f : A → X) (g : B → X) (h : A → B) (H : f ~ (g ∘ h))
    (retraction-g : retraction g) → h ~ ((pr1 retraction-g) ∘ f)
  triangle-retraction f g h H retraction-g =
    inv-htpy (inv-triangle-retraction f g h H retraction-g)
```
