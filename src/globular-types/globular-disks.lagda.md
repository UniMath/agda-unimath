# Globular disks

```agda
{-# OPTIONS --guardedness #-}

module globular-types.globular-disks where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.booleans
open import foundation.unit-type
open import foundation.universe-levels

open import globular-types.empty-globular-types
open import globular-types.globular-suspension
open import globular-types.globular-types
```

</details>

## Idea

The
{{#concept "globular `n`-disk" Disambiguation="globular type" Agda=globular-disk}}
is a [globular type](globular-types.globular-types.md) with the property that
`n`-cells in an arbitrary globular type `G` are equivalently described as
[globular maps](globular-types.globular-maps.md) from the globular `n`-disk into
`G`. In other words, the globular `n`-disk can be thought of as the representing
`n`-cell.

## Definitions

### The globular `0`-disk

```agda
0-cell-globular-0-disk : UU lzero
0-cell-globular-0-disk = unit

1-cell-globular-type-globular-0-disk :
  (x y : 0-cell-globular-0-disk) → Globular-Type lzero lzero
1-cell-globular-type-globular-0-disk x y =
  empty-Globular-Type

globular-0-disk :
  Globular-Type lzero lzero
0-cell-Globular-Type globular-0-disk =
  0-cell-globular-0-disk
1-cell-globular-type-Globular-Type globular-0-disk =
  1-cell-globular-type-globular-0-disk
```

### The globular `n`-disk

```agda
globular-disk : (n : ℕ) → Globular-Type lzero lzero
globular-disk zero-ℕ = globular-0-disk
globular-disk (succ-ℕ n) = suspension-Globular-Type (globular-disk n)
```
