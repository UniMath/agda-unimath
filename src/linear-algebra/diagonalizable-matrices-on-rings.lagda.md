# Diagonalizable matrices on rings

```agda
module linear-algebra.diagonalizable-matrices-on-rings where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.existential-quantification
open import foundation.function-types
open import foundation.subtypes
open import foundation.universe-levels

open import linear-algebra.diagonal-matrices-on-rings
open import linear-algebra.finite-sequences-in-rings
open import linear-algebra.similarity-square-matrices-on-rings
open import linear-algebra.square-matrices-on-rings

open import ring-theory.rings
```

</details>

## Idea

A
{{#concept "diagonalizable matrix" Disambiguation="on a ring" WDID=Q1767080 WD="diagonalizable matrix" Agda=diagonalizable-matrix-Ring}}
on a [ring](ring-theory.rings.md) is a
[square matrix](linear-algebra.square-matrices-on-rings.md) that is
[similar](linear-algebra.similarity-square-matrices-on-rings.md) to a
[diagonal matrix](linear-algebra.diagonal-matrices-on-rings.md).

## Definition

```agda
module _
  {l : Level}
  (R : Ring l)
  (n : ℕ)
  where

  is-diagonalizable-prop-square-matrix-Ring :
    subtype l (square-matrix-Ring R n)
  is-diagonalizable-prop-square-matrix-Ring A =
    ∃ ( diagonal-matrix-Ring R n)
      ( sim-prop-square-matrix-Ring R n A ∘ matrix-diagonal-matrix-Ring R n)

  is-diagonalizable-square-matrix-Ring :
    square-matrix-Ring R n → UU l
  is-diagonalizable-square-matrix-Ring =
    is-in-subtype is-diagonalizable-prop-square-matrix-Ring

  diagonalizable-matrix-Ring : UU l
  diagonalizable-matrix-Ring =
    type-subtype is-diagonalizable-prop-square-matrix-Ring
```
