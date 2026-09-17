# Column matrices on commutative rings

```agda
module linear-algebra.column-matrices-on-commutative-rings where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-rings

open import elementary-number-theory.natural-numbers

open import foundation.equivalences
open import foundation.universe-levels

open import linear-algebra.column-matrices
open import linear-algebra.matrices-on-rings
```

</details>

## Idea

A
{{#concept "column matrix" Disambiguation="on a ring" Agda=column-matrix-Commutative-Ring}}
of length `n` on a [commutative ring](commutative-algebra.commutative-rings.md)
`R` is a [matrix](linear-algebra.matrices-on-commutative-rings.md) on `R` with
`n` rows and one column.

## Definition

```agda
column-matrix-Commutative-Ring : {l : Level} → Commutative-Ring l → ℕ → UU l
column-matrix-Commutative-Ring R n = column-matrix (type-Commutative-Ring R) n
```
