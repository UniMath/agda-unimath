# Column matrices on rings

```agda
module linear-algebra.column-matrices-on-rings where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.equivalences
open import foundation.universe-levels

open import linear-algebra.column-matrices
open import linear-algebra.matrices-on-rings

open import ring-theory.rings
```

</details>

## Idea

A
{{#concept "column matrix" Disambiguation="on a ring" Agda=column-matrix-Ring}}
of length `n` on a [ring](ring-theory.rings.md) `R` is a
[matrix](linear-algebra.matrices-on-rings.md) on `R` with `n` rows and one
column.

## Definition

```agda
column-matrix-Ring : {l : Level} → Ring l → ℕ → UU l
column-matrix-Ring R n = column-matrix (type-Ring R) n
```
