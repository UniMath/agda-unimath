# The universal property of the unit type

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation.universal-property-unit-type where

open import foundation.constant-maps using (const)
open import foundation.contractible-types using
  ( dependent-universal-property-contr-is-contr; is-contr; is-equiv-is-contr)
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.equivalences using
  ( is-equiv; _≃_; is-equiv-is-equiv-precomp; is-equiv-right-factor';
    is-equiv-comp; is-equiv-precomp-is-equiv; is-equiv-is-section)
open import foundation.functions using (precomp)
open import foundation.homotopies using (refl-htpy)
open import foundation.identity-types using (refl)
open import foundation.unit-type using (unit; star; is-contr-unit)
open import foundation.universe-levels using (Level; UU)
```

## Idea

The universal property of the unit type characterizes maps out of the unit type. Similarly, the dependent universal property of the unit type characterizes dependent functions out of the unit type.

In `foundation.contractible-types` we have alread proven related universal properties of contractible types.

## Properties

```agda
-- We conclude that the properties in the exercise hold for the unit type

ev-star :
  {l : Level} (P : unit → UU l) → ((x : unit) → P x) → P star
ev-star P f = f star

ev-star' :
  {l : Level} (Y : UU l) → (unit → Y) → Y
ev-star' Y = ev-star (λ t → Y)

pt : {l1 : Level} {X : UU l1} (x : X) → unit → X
pt x y = x

abstract
  dependent-universal-property-unit :
    {l : Level} (P : unit → UU l) → is-equiv (ev-star P)
  dependent-universal-property-unit =
    dependent-universal-property-contr-is-contr star is-contr-unit

equiv-dependent-universal-property-unit :
  {l : Level} (P : unit → UU l) → ((x : unit) → P x) ≃ P star
pr1 (equiv-dependent-universal-property-unit P) = ev-star P
pr2 (equiv-dependent-universal-property-unit P) =
  dependent-universal-property-unit P

abstract
  universal-property-unit :
    {l : Level} (Y : UU l) → is-equiv (ev-star' Y)
  universal-property-unit Y = dependent-universal-property-unit (λ t → Y)

equiv-universal-property-unit :
  {l : Level} (Y : UU l) → (unit → Y) ≃ Y
pr1 (equiv-universal-property-unit Y) = ev-star' Y
pr2 (equiv-universal-property-unit Y) = universal-property-unit Y

abstract
  is-equiv-pt-is-contr :
    {l1 : Level} {X : UU l1} (x : X) →
    is-contr X → is-equiv (pt x)
  is-equiv-pt-is-contr x is-contr-X =
    is-equiv-is-contr (pt x) is-contr-unit is-contr-X

abstract
  is-equiv-pt-universal-property-unit :
    {l1 : Level} (X : UU l1) (x : X) →
    ((l2 : Level) (Y : UU l2) → is-equiv (λ (f : X → Y) → f x)) →
    is-equiv (pt x)
  is-equiv-pt-universal-property-unit X x H =
    is-equiv-is-equiv-precomp
      ( pt x)
      ( λ l Y → is-equiv-right-factor'
        ( ev-star' Y)
        ( precomp (pt x) Y)
        ( universal-property-unit Y)
        ( H _ Y))

abstract
  universal-property-unit-is-equiv-pt :
    {l1 : Level} {X : UU l1} (x : X) →
    is-equiv (pt x) →
    ({l2 : Level} (Y : UU l2) → is-equiv (λ (f : X → Y) → f x))
  universal-property-unit-is-equiv-pt x is-equiv-pt Y =
    is-equiv-comp
      ( λ f → f x)
      ( ev-star' Y)
      ( precomp (pt x) Y)
      ( λ f → refl)
      ( is-equiv-precomp-is-equiv (pt x) is-equiv-pt Y)
      ( universal-property-unit Y)

abstract
  universal-property-unit-is-contr :
    {l1 : Level} {X : UU l1} (x : X) →
    is-contr X →
    ({l2 : Level} (Y : UU l2) → is-equiv (λ (f : X → Y) → f x))
  universal-property-unit-is-contr x is-contr-X =
    universal-property-unit-is-equiv-pt x
      ( is-equiv-pt-is-contr x is-contr-X)

abstract
  is-equiv-diagonal-is-equiv-pt :
    {l1 : Level} {X : UU l1} (x : X) →
    is-equiv (pt x) →
    ({l2 : Level} (Y : UU l2) → is-equiv (λ y → const X Y y))
  is-equiv-diagonal-is-equiv-pt {X = X} x is-equiv-pt Y =
    is-equiv-is-section
      ( universal-property-unit-is-equiv-pt x is-equiv-pt Y)
      ( refl-htpy)
```
