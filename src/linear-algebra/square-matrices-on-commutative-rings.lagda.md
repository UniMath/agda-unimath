# Square matrices on commutative rings

```agda
module linear-algebra.square-matrices-on-commutative-rings where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-rings

open import elementary-number-theory.natural-numbers

open import foundation.universe-levels

open import linear-algebra.left-modules-commutative-rings
open import linear-algebra.matrices-on-commutative-rings
open import linear-algebra.square-matrices-on-rings
```

</details>

## Idea

A
{{#concept "square matrix" Disambiguation="over a commutative ring" WDID=Q2739329 WD="square matrix" Agda=square-matrix-Commutative-Ring}}
on a [commutative ring](commutative-algebra.commutative-rings.md) `R` of size
`n` is an `n × n` [matrix](linear-algebra.matrices-on-commutative-rings.md) on
`R`.

## Definition

```agda
square-matrix-Commutative-Ring :
  {l : Level} → Commutative-Ring l → ℕ → UU l
square-matrix-Commutative-Ring R = square-matrix-Ring (ring-Commutative-Ring R)
```

## Properties

### Square matrices on a commutative ring form a left module

```agda
module _
  {l : Level}
  (R : Commutative-Ring l)
  (n : ℕ)
  where

  left-module-square-matrix-Commutative-Ring : left-module-Commutative-Ring l R
  left-module-square-matrix-Commutative-Ring =
    left-module-matrix-Commutative-Ring R n n
```
