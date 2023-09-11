# Sections

```agda
module foundation-core.sections where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import foundation-core.function-types
open import foundation-core.homotopies
```

</details>

## Idea

A **section** is a map that has a left inverse, i.e. a retraction. Thus,
`s : B → A` is a section of `f : A → B` if the composition `f ∘ s` is homotopic
to the identity at `B`.

For example, every dependent function induces a section of the projection map.

## Definition

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  where

  section : UU (l1 ⊔ l2)
  section = Σ (B → A) (λ s → (f ∘ s) ~ id)

  map-section : section → B → A
  map-section = pr1

  is-section-map-section : (s : section) → (f ∘ map-section s) ~ id
  is-section-map-section = pr2
```

## Properties

### If `g ∘ f` has a section then `g` has a section

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  where

  section-left-factor :
    (g : B → X) (h : A → B) → section (g ∘ h) → section g
  pr1 (section-left-factor g h section-gh) = h ∘ (pr1 section-gh)
  pr2 (section-left-factor g h section-gh) = pr2 section-gh

  section-left-factor-htpy' :
    (f : A → X) (g : B → X) (h : A → B) (H' : (g ∘ h) ~ f) →
    section f → section g
  pr1 (section-left-factor-htpy' f g h H' section-f) =
    h ∘ (pr1 section-f)
  pr2 (section-left-factor-htpy' f g h H' section-f) =
    (H' ·r pr1 section-f) ∙h (pr2 section-f)

  section-left-factor-htpy :
    (f : A → X) (g : B → X) (h : A → B) (H : f ~ (g ∘ h)) →
    section f → section g
  section-left-factor-htpy f g h H section-f =
    section-left-factor-htpy' f g h (inv-htpy H) section-f
```

### Composites of sections are sections

```agda
  section-comp :
    (g : B → X) (h : A → B) → section h → section g → section (g ∘ h)
  pr1 (section-comp g h section-h section-g) = pr1 section-h ∘ pr1 section-g
  pr2 (section-comp g h section-h section-g) =
    (g ·l (pr2 section-h ·r (pr1 section-g))) ∙h (pr2 section-g)

  section-comp-htpy :
    (f : A → X) (g : B → X) (h : A → B) (H : f ~ (g ∘ h)) →
    section h → section g → section f
  pr1 (section-comp-htpy f g h H section-h section-g) =
    pr1 (section-comp g h section-h section-g)
  pr2 (section-comp-htpy f g h H section-h section-g) =
    (H ·r pr1 (section-comp g h section-h section-g)) ∙h
    (pr2 (section-comp g h section-h section-g))

  inv-triangle-section :
    (f : A → X) (g : B → X) (h : A → B) (H : f ~ (g ∘ h))
    (section-h : section h) → (f ∘ (pr1 section-h)) ~ g
  inv-triangle-section h g f H section-h =
    (H ·r (pr1 section-h)) ∙h (g ·l (pr2 section-h))

  triangle-section :
    (f : A → X) (g : B → X) (h : A → B) (H : f ~ (g ∘ h))
    (section-h : section h) → g ~ (f ∘ (pr1 section-h))
  triangle-section h g f H section-h =
    inv-htpy (inv-triangle-section h g f H section-h)
```
