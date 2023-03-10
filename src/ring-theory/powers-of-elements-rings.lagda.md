# Powers of elements in rings

```agda
module ring-theory.powers-of-elements-rings where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.identity-types
open import foundation.universe-levels

open import ring-theory.powers-of-elements-semirings
open import ring-theory.rings
```

</details>

## Idea

The power operation on a ring is the map `n x ↦ xⁿ`, which is defined by iteratively multiplying `x` with itself `n` times.

## Definition

```agda
power-Ring : {l : Level} (R : Ring l) → ℕ → type-Ring R → type-Ring R
power-Ring R = power-Semiring (semiring-Ring R)
```

## Properties

### `xⁿ⁺¹ = xⁿx`

```agda
module _
  {l : Level} (R : Ring l)
  where

  power-succ-Ring :
    (n : ℕ) (x : type-Ring R) →
    power-Ring R (succ-ℕ n) x ＝ mul-Ring R (power-Ring R n x) x
  power-succ-Ring = power-succ-Semiring (semiring-Ring R)
```

### If `x` commutes with `y` then so do their powers

```agda
module _
  {l : Level} (R : Ring l)
  where

  commute-powers-Ring' :
    (n : ℕ) {x y : type-Ring R} →
    ( mul-Ring R x y ＝ mul-Ring R y x) →
    ( mul-Ring R (power-Ring R n x) y) ＝
    ( mul-Ring R y (power-Ring R n x))
  commute-powers-Ring' = commute-powers-Semiring' (semiring-Ring R)

  commute-powers-Ring :
    (m n : ℕ) {x y : type-Ring R} → mul-Ring R x y ＝ mul-Ring R y x →
    ( mul-Ring R (power-Ring R m x) (power-Ring R n y)) ＝
    ( mul-Ring R (power-Ring R n y) (power-Ring R m x))
  commute-powers-Ring = commute-powers-Semiring (semiring-Ring R)
```
