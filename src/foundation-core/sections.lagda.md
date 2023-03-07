# Sections

```agda
{-# OPTIONS --safe #-}
```

```agda
module foundation-core.sections where
```

<details><summary>Imports</summary>

```agda
open import foundation-core.dependent-pair-types
open import foundation-core.functions
open import foundation-core.homotopies
open import foundation-core.universe-levels
```

</details>

## Idea

Any dependent function induces a section of the projection map

## Definition

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  sec : (A → B) → UU (l1 ⊔ l2)
  sec f = Σ (B → A) (λ g → (f ∘ g) ~ id)
```

## Properties

### If `g ∘ f` has a section then `g` has a section

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  where

  section-left-factor :
    (g : B → X) (h : A → B) → sec (g ∘ h) → sec g
  pr1 (section-left-factor g h sec-gh) = h ∘ (pr1 sec-gh)
  pr2 (section-left-factor g h sec-gh) = pr2 sec-gh

  section-left-factor-htpy' :
    (f : A → X) (g : B → X) (h : A → B) (H' : (g ∘ h) ~ f) →
    sec f → sec g
  pr1 (section-left-factor-htpy' f g h H' sec-f) =
    h ∘ (pr1 sec-f)
  pr2 (section-left-factor-htpy' f g h H' sec-f) =
    (H' ·r pr1 sec-f) ∙h (pr2 sec-f)

  section-left-factor-htpy :
    (f : A → X) (g : B → X) (h : A → B) (H : f ~ (g ∘ h)) →
    sec f → sec g
  section-left-factor-htpy f g h H sec-f =
    section-left-factor-htpy' f g h (inv-htpy H) sec-f
```

### Composites of sections are sections

```agda
  section-comp :
    (g : B → X) (h : A → B) → sec h → sec g → sec (g ∘ h)
  pr1 (section-comp g h sec-h sec-g) = pr1 sec-h ∘ pr1 sec-g
  pr2 (section-comp g h sec-h sec-g) =
    (g ·l (pr2 sec-h ·r (pr1 sec-g))) ∙h (pr2 sec-g)

  section-comp-htpy :
    (f : A → X) (g : B → X) (h : A → B) (H : f ~ (g ∘ h)) →
    sec h → sec g → sec f
  pr1 (section-comp-htpy f g h H sec-h sec-g) =
    pr1 (section-comp g h sec-h sec-g)
  pr2 (section-comp-htpy f g h H sec-h sec-g) =
    (H ·r pr1 (section-comp g h sec-h sec-g)) ∙h
    (pr2 (section-comp g h sec-h sec-g))

  inv-triangle-section :
    (f : A → X) (g : B → X) (h : A → B) (H : f ~ (g ∘ h))
    (sec-h : sec h) → (f ∘ (pr1 sec-h)) ~ g
  inv-triangle-section h g f H sec-h =
    (H ·r (pr1 sec-h)) ∙h (g ·l (pr2 sec-h))

  triangle-section :
    (f : A → X) (g : B → X) (h : A → B) (H : f ~ (g ∘ h))
    (sec-h : sec h) → g ~ (f ∘ (pr1 sec-h))
  triangle-section h g f H sec-h =
    inv-htpy (inv-triangle-section h g f H sec-h)
```
