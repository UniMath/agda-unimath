---
title: Sections of type families
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

### Composites of sections are sections

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (f : A → X) (g : B → X) (h : A → B) (H : f ~ (g ∘ h))
  where

  triangle-section : (S : sec h) → g ~ (f ∘ (pr1 S))
  triangle-section (pair s issec) = inv-htpy ((H ·r s) ∙h (g ·l issec))

  section-comp : sec h → sec f → sec g
  pr1 (section-comp sec-h sec-f) = h ∘ (pr1 sec-f)
  pr2 (section-comp sec-h sec-f) = (inv-htpy (H ·r (pr1 sec-f))) ∙h (pr2 sec-f)
  
  section-comp' : sec h → sec g → sec f
  pr1 (section-comp' sec-h sec-g) = (pr1 sec-h) ∘ (pr1 sec-g)
  pr2 (section-comp' sec-h sec-g) =
    ( H ·r ((pr1 sec-h) ∘ (pr1 sec-g))) ∙h
    ( ( g ·l ((pr2 sec-h) ·r (pr1 sec-g))) ∙h ((pr2 sec-g)))
```
 