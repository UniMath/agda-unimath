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
gap-unit-Pointed-Type : {l : Level} (X : Pointed-Type l) → X →* unit-Pointed-Type
pr1 (gap-unit-Pointed-Type X) _ = star
pr2 (gap-unit-Pointed-Type X) = refl

cogap-unit-Pointed-Type : {l : Level} (X : Pointed-Type l) → unit-Pointed-Type →* X
pr1 (cogap-unit-Pointed-Type X) _ = point-Pointed-Type X
pr2 (cogap-unit-Pointed-Type X) = refl
```
