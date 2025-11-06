# Globular suspension

```agda
{-# OPTIONS --guardedness #-}

module globular-types.globular-suspension where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels

open import globular-types.empty-globular-types
open import globular-types.globular-types
```

</details>

## Idea

The
{{#concept "globular suspension" Disambiguation="globular type" Agda=suspension-Globular-Type}}
of a [globular type](globular-types.globular-types.md) `G` is a globular type
`ΣG` with exactly two `0`-cells called north and south, and a
[globular map](globular-types.globular-maps.md) from G to the globular type of
`1`-cells from north to south in `ΣG`.

## Definition

### The suspension of globular sets of a fixed universe level `l1`

Note: Allowing globular types with separate universe levels for 0-cells and
higher cells complicates the definition of suspension.

```agda
module _
  {l1 : Level} (G : Globular-Type l1 l1)
  where

  data 0-cell-suspension-Globular-Type : UU lzero where
    north-suspension-Globular-Type : 0-cell-suspension-Globular-Type
    south-suspension-Globular-Type : 0-cell-suspension-Globular-Type

  suspension-Globular-Type : Globular-Type lzero l1
  0-cell-Globular-Type suspension-Globular-Type =
    0-cell-suspension-Globular-Type
  1-cell-globular-type-Globular-Type
    suspension-Globular-Type
    north-suspension-Globular-Type
    north-suspension-Globular-Type =
    raise-empty-Globular-Type l1 l1
  1-cell-globular-type-Globular-Type
    suspension-Globular-Type
    north-suspension-Globular-Type
    south-suspension-Globular-Type =
    G
  1-cell-globular-type-Globular-Type
    suspension-Globular-Type
    south-suspension-Globular-Type
    north-suspension-Globular-Type =
    raise-empty-Globular-Type l1 l1
  1-cell-globular-type-Globular-Type
    suspension-Globular-Type
    south-suspension-Globular-Type
    south-suspension-Globular-Type =
    raise-empty-Globular-Type l1 l1
```
