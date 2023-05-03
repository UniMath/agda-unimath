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

open import structured-types.pointed-maps
open import structured-types.pointed-types
```

</details>

## Idea

The pointed unit type is the initial pointed type.

## Definition

```agda
unit-Pointed-Type : Pointed-Type lzero
pr1 unit-Pointed-Type = unit
pr2 unit-Pointed-Type = star
```

## Properties

```agda
terminal-pointed-map : {l : Level} (X : Pointed-Type l) → X →∗ unit-Pointed-Type
pr1 (terminal-pointed-map X) _ = star
pr2 (terminal-pointed-map X) = refl

inclusion-point-Pointed-Type :
  {l : Level} (X : Pointed-Type l) → unit-Pointed-Type →∗ X
pr1 (inclusion-point-Pointed-Type X) = point (point-Pointed-Type X)
pr2 (inclusion-point-Pointed-Type X) = refl
```
