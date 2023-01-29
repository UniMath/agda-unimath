---
title: Sections
---

```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module foundation-core.sections where

open import foundation-core.dependent-pair-types
open import foundation-core.functions using (_∘_; id)
open import foundation-core.homotopies
open import foundation-core.universe-levels
```

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
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  where
  
  section-left-factor :
    (f : A → B) (g : B → C) → sec (g ∘ f) → sec g
  pr1 (section-left-factor f g sec-gf) = f ∘ (pr1 sec-gf)
  pr2 (section-left-factor f g sec-gf) = pr2 sec-gf

  section-left-factor-htpy' :
    (f : A → B) (g : B → C) (h : A → C) (H' : (g ∘ f) ~ h) →
    sec h → sec g
  pr1 (section-left-factor-htpy' f g h H' sec-h) =
    f ∘ (pr1 sec-h)
  pr2 (section-left-factor-htpy' f g h H' sec-h) =
    (H' ·r pr1 sec-h) ∙h (pr2 sec-h)

  section-left-factor-htpy :
    (f : A → B) (g : B → C) (h : A → C) (H : h ~ (g ∘ f)) →
    sec h → sec g
  section-left-factor-htpy f g h H sec-h =
    section-left-factor-htpy' f g h (inv-htpy H) sec-h
```

### Composites of sections are sections

```agda
  section-comp :
    (f : A → B) (g : B → C) → sec f → sec g → sec (g ∘ f)
  pr1 (section-comp f g sec-f sec-g) = pr1 sec-f ∘ pr1 sec-g
  pr2 (section-comp f g sec-f sec-g) =
    (g ·l (pr2 sec-f ·r (pr1 sec-g))) ∙h (pr2 sec-g)

  section-comp-htpy :
    (f : A → B) (g : B → C) (h : A → C) (H : h ~ (g ∘ f)) →
    sec f → sec g → sec h
  pr1 (section-comp-htpy f g h H sec-f sec-g) =
    pr1 (section-comp f g sec-f sec-g)
  pr2 (section-comp-htpy f g h H sec-f sec-g) =
    (H ·r pr1 (section-comp f g sec-f sec-g)) ∙h
    (pr2 (section-comp f g sec-f sec-g))


  inv-triangle-section :
    (h : A → C) (g : B → C) (f : A → B) (H : h ~ (g ∘ f))
    (sec-f : sec f) → (h ∘ (pr1 sec-f)) ~ g 
  inv-triangle-section h g f H sec-f =
    (H ·r (pr1 sec-f)) ∙h (g ·l (pr2 sec-f))

  triangle-section :
    (h : A → C) (g : B → C) (f : A → B) (H : h ~ (g ∘ f))
    (sec-f : sec f) → g ~ (h ∘ (pr1 sec-f))
  triangle-section h g f H sec-f =
    inv-htpy (inv-triangle-section h g f H sec-f)
```
 