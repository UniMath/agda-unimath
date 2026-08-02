# Invertible matrices on rings

```agda
module linear-algebra.invertible-matrices-on-rings where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.subtypes
open import foundation.universe-levels

open import group-theory.invertible-elements-monoids

open import linear-algebra.multiplication-square-matrices-on-rings
open import linear-algebra.square-matrices-on-rings

open import ring-theory.rings
```

</details>

## Idea

An `n × n` [square matrix](linear-algebra.square-matrices-on-rings.md) on a
[ring](ring-theory.rings.md) is
{{#concept "invertible" WDID=Q242188 WD="invertible matrix" Disambiguation="square matrix over a ring" Agda=is-invertible-square-matrix-Ring}}
if it is [invertible](group-theory.invertible-elements-monoids.md) in the
[monoid of square matrix multiplication](linear-algebra.multiplication-square-matrices-on-rings.md).

## Definition

```agda
module _
  {l : Level}
  (R : Ring l)
  (n : ℕ)
  where

  is-invertible-prop-square-matrix-Ring :
    subtype l (square-matrix-Ring R n)
  is-invertible-prop-square-matrix-Ring =
    is-invertible-element-prop-Monoid (monoid-mul-square-matrix-Ring R n)

  is-invertible-square-matrix-Ring :
    square-matrix-Ring R n → UU l
  is-invertible-square-matrix-Ring =
    is-in-subtype is-invertible-prop-square-matrix-Ring

  invertible-matrix-Ring : UU l
  invertible-matrix-Ring =
    type-subtype is-invertible-prop-square-matrix-Ring

module _
  {l : Level}
  (R : Ring l)
  (n : ℕ)
  ((M , M⁻¹ , is-inv-M⁻¹) : invertible-matrix-Ring R n)
  where

  matrix-invertible-matrix-Ring : square-matrix-Ring R n
  matrix-invertible-matrix-Ring = M

  is-invertible-matrix-invertible-matrix-Ring :
    is-invertible-square-matrix-Ring R n matrix-invertible-matrix-Ring
  is-invertible-matrix-invertible-matrix-Ring = (M⁻¹ , is-inv-M⁻¹)

  matrix-inv-invertible-matrix-Ring : square-matrix-Ring R n
  matrix-inv-invertible-matrix-Ring = M⁻¹

  is-invertible-matrix-inv-invertible-matrix-Ring :
    is-invertible-square-matrix-Ring R n matrix-inv-invertible-matrix-Ring
  is-invertible-matrix-inv-invertible-matrix-Ring =
    is-invertible-element-inverse-Monoid
      ( monoid-mul-square-matrix-Ring R n)
      ( M)
      ( M⁻¹ , is-inv-M⁻¹)

  invertible-matrix-inv-invertible-matrix-Ring : invertible-matrix-Ring R n
  invertible-matrix-inv-invertible-matrix-Ring =
    ( M⁻¹ , is-invertible-matrix-inv-invertible-matrix-Ring)
```
