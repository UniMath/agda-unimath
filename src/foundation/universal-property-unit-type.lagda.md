# The universal property of the unit type

```agda
module foundation.universal-property-unit-type where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.diagonal-maps-of-types
open import foundation.unit-type
open import foundation.universal-property-contractible-types
open import foundation.universal-property-equivalences
open import foundation.universe-levels

open import foundation-core.constant-maps
open import foundation-core.contractible-types
open import foundation-core.equivalences
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.precomposition-functions
open import foundation-core.retractions
open import foundation-core.sections
```

</details>

## Idea

The universal property of the unit type characterizes maps out of the unit type.
Similarly, the dependent universal property of the unit type characterizes
dependent functions out of the unit type.

In `foundation.contractible-types` we have already proven related universal
properties of contractible types.

## Properties

```agda
ev-star :
  {l : Level} (P : unit → UU l) → ((x : unit) → P x) → P star
ev-star P f = f star

ev-star' :
  {l : Level} (Y : UU l) → (unit → Y) → Y
ev-star' Y = ev-star (λ _ → Y)

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

module _
  {l : Level} (Y : UU l)
  where

  is-section-const-unit : is-section (ev-star' Y) (const unit)
  is-section-const-unit = refl-htpy

  is-retraction-const-unit : is-retraction (ev-star' Y) (const unit)
  is-retraction-const-unit = refl-htpy

  universal-property-unit : is-equiv (ev-star' Y)
  universal-property-unit =
    is-equiv-is-invertible
      ( const unit)
      ( is-section-const-unit)
      ( is-retraction-const-unit)

  equiv-universal-property-unit : (unit → Y) ≃ Y
  equiv-universal-property-unit = (ev-star' Y , universal-property-unit)

  is-equiv-const-unit : is-equiv (const unit)
  is-equiv-const-unit =
    is-equiv-is-invertible
      ( ev-star' Y)
      ( is-retraction-const-unit)
      ( is-section-const-unit)

  inv-equiv-universal-property-unit : Y ≃ (unit → Y)
  inv-equiv-universal-property-unit = (const unit , is-equiv-const-unit)

abstract
  is-equiv-point-is-contr :
    {l1 : Level} {X : UU l1} (x : X) →
    is-contr X → is-equiv (point x)
  is-equiv-point-is-contr x is-contr-X =
    is-equiv-is-contr (point x) is-contr-unit is-contr-X

abstract
  is-equiv-point-universal-property-unit :
    {l1 : Level} (X : UU l1) (x : X) →
    ({l2 : Level} (Y : UU l2) → is-equiv (λ (f : X → Y) → f x)) →
    is-equiv (point x)
  is-equiv-point-universal-property-unit X x H =
    is-equiv-is-equiv-precomp
      ( point x)
      ( λ Y →
        is-equiv-right-factor
          ( ev-star' Y)
          ( precomp (point x) Y)
          ( universal-property-unit Y)
          ( H Y))

abstract
  universal-property-unit-is-equiv-point :
    {l1 : Level} {X : UU l1} (x : X) →
    is-equiv (point x) →
    ({l2 : Level} (Y : UU l2) → is-equiv (λ (f : X → Y) → f x))
  universal-property-unit-is-equiv-point x is-equiv-point Y =
    is-equiv-comp
      ( ev-star' Y)
      ( precomp (point x) Y)
      ( is-equiv-precomp-is-equiv (point x) is-equiv-point Y)
      ( universal-property-unit Y)

abstract
  universal-property-unit-is-contr :
    {l1 : Level} {X : UU l1} (x : X) →
    is-contr X →
    ({l2 : Level} (Y : UU l2) → is-equiv (λ (f : X → Y) → f x))
  universal-property-unit-is-contr x is-contr-X =
    universal-property-unit-is-equiv-point x
      ( is-equiv-point-is-contr x is-contr-X)

abstract
  is-equiv-diagonal-exponential-is-equiv-point :
    {l1 : Level} {X : UU l1} (x : X) →
    is-equiv (point x) →
    ({l2 : Level} (Y : UU l2) → is-equiv (diagonal-exponential Y X))
  is-equiv-diagonal-exponential-is-equiv-point x is-equiv-point Y =
    is-equiv-is-section
      ( universal-property-unit-is-equiv-point x is-equiv-point Y)
      ( refl-htpy)
```

### Precomposition with the terminal map is an equivalence if and only if the diagonal exponential is

```agda
is-equiv-precomp-terminal-map-is-equiv-diagonal-exponential :
  {l1 l2 : Level} {X : UU l1} {U : UU l2} →
  is-equiv (diagonal-exponential U X) →
  is-equiv (precomp (terminal-map X) U)
is-equiv-precomp-terminal-map-is-equiv-diagonal-exponential H =
  is-equiv-left-factor _ _ H (is-equiv-const-unit _)

is-equiv-diagonal-exponential-is-equiv-precomp-terminal-map :
  {l1 l2 : Level} {X : UU l1} {U : UU l2} →
  is-equiv (precomp (terminal-map X) U) →
  is-equiv (diagonal-exponential U X)
is-equiv-diagonal-exponential-is-equiv-precomp-terminal-map H =
  is-equiv-comp _ _ (is-equiv-const-unit _) H
```
