# The pointed unit type

```agda
module structured-types.pointed-unit-type where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.unit-type
open import foundation.universe-levels

open import structured-types.pointed-homotopies
open import structured-types.pointed-maps
open import structured-types.pointed-types
```

</details>

## Idea

The {{#concept "pointed unit type" Agda=unit-Pointed-Type}} is the initial
pointed type.

## Definition

```agda
unit-Pointed-Type : Pointed-Type lzero
unit-Pointed-Type = (unit , star)
```

## Properties

```agda
module _
  {l : Level} (X : Pointed-Type l)
  where

  terminal-pointed-map : X →∗ unit-Pointed-Type
  pr1 terminal-pointed-map _ = star
  pr2 terminal-pointed-map = refl

  map-terminal-pointed-map : type-Pointed-Type X → unit
  map-terminal-pointed-map =
    map-pointed-map {A = X} {B = unit-Pointed-Type}
      terminal-pointed-map

  inclusion-point-Pointed-Type : unit-Pointed-Type →∗ X
  pr1 inclusion-point-Pointed-Type = point (point-Pointed-Type X)
  pr2 inclusion-point-Pointed-Type = refl

  is-initial-unit-Pointed-Type :
    ( f : unit-Pointed-Type →∗ X) → f ~∗ inclusion-point-Pointed-Type
  pr1 (is-initial-unit-Pointed-Type f) _ = preserves-point-pointed-map f
  pr2 (is-initial-unit-Pointed-Type f) = inv right-unit
```
