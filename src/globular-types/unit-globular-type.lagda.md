# The unit globular type

```agda
{-# OPTIONS --guardedness #-}

module globular-types.unit-globular-type where
```

<details><summary>Imports</summary>

```agda
open import foundation.unit-type
open import foundation.universe-levels

open import globular-types.constant-globular-types
open import globular-types.globular-types
```

</details>

## Idea

The {{#concept "unit globular type" Agda=unit-Globular-Type}} is the
[constant globular type](globular-types.constant-globular-types.md) at the
[unit type](foundation.unit-type.md). That is, the unit globular type is the
[globular type](globular-types.globular-types.md) `𝟏` given by

```text
  𝟏₀ := unit
  𝟏' x y := 𝟏.
```

## Definitions

### The unit globular type

```agda
unit-Globular-Type : Globular-Type lzero lzero
unit-Globular-Type = constant-Globular-Type unit
```
