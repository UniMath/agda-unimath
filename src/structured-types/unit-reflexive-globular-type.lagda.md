# The unit reflexive globular type

```agda
{-# OPTIONS --guardedness #-}

module structured-types.unit-reflexive-globular-type where
```

<details><summary>Imports</summary>

```agda
open import foundation.unit-type
open import foundation.universe-levels

open import structured-types.reflexive-globular-types
open import structured-types.unit-globular-type
```

</details>

## Idea

The
{{#concept "unit reflexive globular type" Agda=unit-Reflexive-Globular-Type}} is
the [reflexive globular type](structured-types.reflexive-globular-types.md) `𝟏`
given by

```text
  𝟏₀ := unit
  𝟏' x y := 𝟏
  𝟏ᵣ x := star.
```

## Definitions

### The unit reflexive globular type

```agda
is-reflexive-unit-Globular-Type :
  is-reflexive-Globular-Type unit-Globular-Type
is-reflexive-1-cell-is-reflexive-Globular-Type
  is-reflexive-unit-Globular-Type x =
  star
is-reflexive-1-cell-globular-type-is-reflexive-Globular-Type
  is-reflexive-unit-Globular-Type =
  is-reflexive-unit-Globular-Type

unit-Reflexive-Globular-Type : Reflexive-Globular-Type lzero lzero
globular-type-Reflexive-Globular-Type unit-Reflexive-Globular-Type =
  unit-Globular-Type
refl-Reflexive-Globular-Type unit-Reflexive-Globular-Type =
  is-reflexive-unit-Globular-Type
```
