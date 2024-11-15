# Constant globular types

```agda
{-# OPTIONS --guardedness #-}

module structured-types.constant-globular-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels

open import structured-types.globular-types
```

</details>

## Idea

Consider a type `A`. The
{{#concept "constant globular type" Agda=constant-Globular-Type}} at `A` is the
[globular type](structured-types.globular-types.md) `𝐀` given by

```text
  𝐀₀ := A
  𝐀₁ x y := 𝐀.
```

## Definitions

### The constant globular type at a type

```agda
module _
  {l : Level} (A : UU l)
  where

  constant-Globular-Type : Globular-Type l l
  0-cell-Globular-Type constant-Globular-Type =
    A
  1-cell-globular-type-Globular-Type constant-Globular-Type x y =
    constant-Globular-Type
```
