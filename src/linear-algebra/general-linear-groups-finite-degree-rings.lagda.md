# The general linear groups of finite degree over rings

```agda
module linear-algebra.general-linear-groups-finite-degree-rings where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.universe-levels

open import group-theory.groups

open import linear-algebra.rings-of-square-matrices-on-rings

open import ring-theory.groups-of-units-rings
open import ring-theory.rings
```

</details>

## Idea

The
{{#concept "general linear group" Disambiguation="of finite degree over a ring" WDID=Q524607 WD="general linear group" Agda=general-linear-group-Ring}}
of degree `n : ℕ` over a [ring](ring-theory.rings.md) `R` is the
[group of units](ring-theory.groups-of-units-rings.md) of the
[ring of `n × n` square matrices](linear-algebra.rings-of-square-matrices-on-rings.md)
on `R`.

## Definition

```agda
general-linear-group-Ring : {l : Level} → ℕ → Ring l → Group l
general-linear-group-Ring n R =
  group-of-units-Ring (ring-square-matrix-Ring R n)
```

## External links

- [General linear group](https://en.wikipedia.org/wiki/General_linear_group) on
  Wikipedia
