# Sections of dependent type theories

```agda
{-# OPTIONS --guardedness #-}

module type-theories.sections-dependent-type-theories where
```

<details><summary>Imports</summary>

```agda
open import foundation.identity-types
open import foundation.transport
open import foundation.universe-levels

open import type-theories.dependent-type-theories
open import type-theories.fibered-dependent-type-theories
```

</details>

```agda
open dependent
open fibered

module sections-dtt where

  precomp-fibered-system :
    {l1 l2 l3 l4 l5 l6 : Level}
    {A : system l1 l2} {B : system l3 l4}
    (C : fibered-system l5 l6 B) (f : hom-system A B) →
    fibered-system l5 l6 A
  fibered-system.type (precomp-fibered-system C f) X =
    fibered-system.type C (section-system.type f X)
  fibered-system.element (precomp-fibered-system C f) Y x =
    fibered-system.element C Y (section-system.element f x)
  fibered-system.slice (precomp-fibered-system C f) {X} Y =
    precomp-fibered-system
      ( fibered-system.slice C Y)
      ( section-system.slice f X)

  precomp-section-system :
    {l1 l2 l3 l4 l5 l6 : Level}
    {A : system l1 l2} {B : system l3 l4}
    {C : fibered-system l5 l6 B}
    (g : section-system C) (f : hom-system A B) →
    section-system (precomp-fibered-system C f)
  section-system.type (precomp-section-system g f) X =
    section-system.type g (section-system.type f X)
  section-system.element (precomp-section-system g f) x =
    section-system.element g (section-system.element f x)
  section-system.slice (precomp-section-system g f) X =
    precomp-section-system
      ( section-system.slice g (section-system.type f X))
      ( section-system.slice f X)

  transpose-bifibered-system :
    {l1 l2 l3 l4 l5 l6 l7 l8 : Level}
    {A : system l1 l2}
    {B : fibered-system l3 l4 A} {C : fibered-system l5 l6 A}
    (D : bifibered-system l7 l8 B C) →
    bifibered-system l7 l8 C B
  bifibered-system.type (transpose-bifibered-system D) Z Y =
    bifibered-system.type D Y Z
  bifibered-system.element (transpose-bifibered-system D) W z y =
    bifibered-system.element D W y z
  bifibered-system.slice (transpose-bifibered-system D) W =
    transpose-bifibered-system (bifibered-system.slice D W)

  postcomp-section-system :
    {l1 l2 l3 l4 l5 l6 l7 l8 : Level}
    {A : system l1 l2} {B : fibered-system l3 l4 A}
    {C : system l5 l6} {D : fibered-system l7 l8 C}
    {f : hom-system A C} (g : hom-fibered-system f B D)
    (h : section-system B) → section-system (precomp-fibered-system D f)
  section-system.type (postcomp-section-system g h) X =
    section-fibered-system.type g (section-system.type h X)
  section-system.element (postcomp-section-system g h) x =
    section-fibered-system.element g (section-system.element h x)
  section-system.slice (postcomp-section-system g h) X =
    postcomp-section-system
      ( section-fibered-system.slice g (section-system.type h X))
      ( section-system.slice h X)

  record preserves-weakening-section-system
    {l1 l2 l3 l4 : Level} {A : system l1 l2} {B : fibered-system l3 l4 A}
    {WA : weakening A} (WB : fibered-weakening B WA)
    (f : section-system B) : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
    where
    coinductive
    field
      type :
        (X : system.type A) →
        htpy-section-system
          ( precomp-section-system
            ( section-system.slice f X)
            ( weakening.type WA X))
          ( postcomp-section-system
            ( fibered-weakening.type WB (section-system.type f X))
            ( f))
      slice :
        (X : system.type A) →
        preserves-weakening-section-system
          ( fibered-weakening.slice WB (section-system.type f X))
          ( section-system.slice f X)

  record preserves-substitution-section-system
    {l1 l2 l3 l4 : Level}
    {A : system l1 l2} {B : fibered-system l3 l4 A}
    {SA : substitution A} (SB : fibered-substitution B SA)
    (f : section-system B) : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
    where
    coinductive
    field
      type :
        {X : system.type A} (x : system.element A X) →
        htpy-section-system
          ( precomp-section-system f (substitution.type SA x))
          ( postcomp-section-system
            ( fibered-substitution.type SB (section-system.element f x))
            ( section-system.slice f X))
      slice :
        (X : system.type A) →
        preserves-substitution-section-system
          ( fibered-substitution.slice SB (section-system.type f X))
          ( section-system.slice f X)

  record preserves-generic-element-section-system
    {l1 l2 l3 l4 : Level}
    {A : system l1 l2} {B : fibered-system l3 l4 A}
    {WA : weakening A} {δA : generic-element WA}
    {WB : fibered-weakening B WA} (δB : fibered-generic-element WB δA)
    {f : section-system B} (Wf : preserves-weakening-section-system WB f) :
    UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
    where
    coinductive
    field
      type :
        (X : system.type A) →
        Id
          ( tr
            ( λ t →
              fibered-system.element
                ( fibered-system.slice B (section-system.type f X))
                ( t)
                ( generic-element.type δA X))
            ( section-system.type
              ( preserves-weakening-section-system.type Wf X)
              ( X))
            ( section-system.element
              ( section-system.slice f X)
              ( generic-element.type δA X)))
            ( fibered-generic-element.type δB (section-system.type f X))
      slice :
        (X : system.type A) →
        preserves-generic-element-section-system
          ( fibered-generic-element.slice δB (section-system.type f X))
          ( preserves-weakening-section-system.slice Wf X)

  record section-type-theory
    {l1 l2 l3 l4 : Level}
    {A : type-theory l1 l2}
    (B : fibered-type-theory l3 l4 A) : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
    where
    field
      sys : section-system (fibered-type-theory.sys B)
      W :
        preserves-weakening-section-system
          ( fibered-type-theory.W B)
          ( sys)
      S :
        preserves-substitution-section-system
          ( fibered-type-theory.S B)
          ( sys)
      δ :
        preserves-generic-element-section-system
          ( fibered-type-theory.δ B)
          ( W)
```
