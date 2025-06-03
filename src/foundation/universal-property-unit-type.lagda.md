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
open import foundation-core.precomposition-functions
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
ev-star' Y = ev-star (λ t → Y)

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

inv-equiv-universal-property-unit :
  {l : Level} (Y : UU l) → Y ≃ (unit → Y)
inv-equiv-universal-property-unit Y =
  inv-equiv (equiv-universal-property-unit Y)

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

### The unit type is terminal

```agda
module _
  {l : Level} {X : UU l}
  where

  is-equiv-terminal-map-Π-unit : is-equiv (terminal-map (X → unit))
  is-equiv-terminal-map-Π-unit =
    is-equiv-is-invertible (const X) refl-htpy refl-htpy
```
