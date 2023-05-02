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
pointed-unit : Pointed-Type lzero
pr1 pointed-unit = unit
pr2 pointed-unit = star
```

## Properties

```agda
gap-pointed-unit : {l : Level} (X : Pointed-Type l) → X →* pointed-unit
pr1 (gap-pointed-unit X) _ = star
pr2 (gap-pointed-unit X) = refl

cogap-pointed-unit : {l : Level} (X : Pointed-Type l) → pointed-unit →* X
pr1 (cogap-pointed-unit X) _ = point-Pointed-Type X
pr2 (cogap-pointed-unit X) = refl
```
