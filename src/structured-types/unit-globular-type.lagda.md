# The unit globular type

```agda
{-# OPTIONS --guardedness #-}

module structured-types.unit-globular-type where
```

<details><summary>Imports</summary>

```agda
open import foundation.unit-type
open import foundation.universe-levels

open import structured-types.globular-types
```

</details>

## Idea

The {{#concept "unit globular type" Agda=unit-Globular-Type}} is the
[globular type](structured-types.globular-types.md) `𝟏` given by

```text
  𝟏₀ := unit
  𝟏' x y := 𝟏.
```

## Definitions

### The unit globular type

```agda
unit-Globular-Type : Globular-Type lzero lzero
0-cell-Globular-Type unit-Globular-Type = unit
1-cell-globular-type-Globular-Type unit-Globular-Type x y = unit-Globular-Type
```
