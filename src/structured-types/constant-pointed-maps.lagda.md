# Constant pointed maps

```agda
module structured-types.constant-pointed-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.constant-maps
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.universe-levels

open import structured-types.pointed-maps
open import structured-types.pointed-types
```

</details>

## Idea

Given two [pointed types](structured-types.pointed-types.md) `A` and `B`, the
{{#concept "constant pointed map" Agda=constant-pointed-map}} from `A` to `B` is
the [pointed map](structured-types.pointed-maps.md)
`constant-pointed-map : A →∗ B` mapping every element in `A` to the base point
of `B`.

## Definitions

### Constant pointed maps

```agda
module _
  {l1 l2 : Level} (A : Pointed-Type l1) (B : Pointed-Type l2)
  where

  map-constant-pointed-map : type-Pointed-Type A → type-Pointed-Type B
  map-constant-pointed-map =
    const (type-Pointed-Type A) (point-Pointed-Type B)

  preserves-point-constant-pointed-map :
    map-constant-pointed-map (point-Pointed-Type A) ＝ point-Pointed-Type B
  preserves-point-constant-pointed-map = refl

  constant-pointed-map : A →∗ B
  pr1 constant-pointed-map = map-constant-pointed-map
  pr2 constant-pointed-map = preserves-point-constant-pointed-map
```

### The pointed type of pointed maps

```agda
module _
  {l1 l2 : Level} (A : Pointed-Type l1) (B : Pointed-Type l2)
  where

  pointed-map-Pointed-Type : Pointed-Type (l1 ⊔ l2)
  pr1 pointed-map-Pointed-Type = A →∗ B
  pr2 pointed-map-Pointed-Type = constant-pointed-map A B
```

## See also

- [Constant maps](foundation.constant-maps.md)
