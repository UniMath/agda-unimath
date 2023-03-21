# Powers of elements in commutative rings

```agda
module commutative-algebra.powers-of-elements-commutative-rings where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-rings

open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.parity-natural-numbers

open import foundation.identity-types
open import foundation.universe-levels

open import ring-theory.powers-of-elements-rings
```

</details>

## Idea

The power operation on a commutative ring is the map `n x ↦ xⁿ`, which is
defined by iteratively multiplying `x` with itself `n` times.

## Definition

```agda
power-Commutative-Ring :
  {l : Level} (R : Commutative-Ring l) →
  ℕ → type-Commutative-Ring R → type-Commutative-Ring R
power-Commutative-Ring R = power-Ring (ring-Commutative-Ring R)
```

## Properties

### `xⁿ⁺¹ = xⁿx`

```agda
module _
  {l : Level} (R : Commutative-Ring l)
  where

  power-succ-Commutative-Ring :
    (n : ℕ) (x : type-Commutative-Ring R) →
    power-Commutative-Ring R (succ-ℕ n) x ＝
    mul-Commutative-Ring R (power-Commutative-Ring R n x) x
  power-succ-Commutative-Ring =
    power-succ-Ring (ring-Commutative-Ring R)
```

### Powers by sums of natural numbers are products of powers

```agda
module _
  {l : Level} (R : Commutative-Ring l)
  where

  power-add-Commutative-Ring :
    (m n : ℕ) {x : type-Commutative-Ring R} →
    power-Commutative-Ring R (add-ℕ m n) x ＝
    mul-Commutative-Ring R
      ( power-Commutative-Ring R m x)
      ( power-Commutative-Ring R n x)
  power-add-Commutative-Ring = power-add-Ring (ring-Commutative-Ring R)
```

### Powers distribute over multiplication

```agda
module _
  {l : Level} (R : Commutative-Ring l)
  where

  distributive-power-mul-Commutative-Ring :
    (n : ℕ) (x y : type-Commutative-Ring R) →
    power-Commutative-Ring R n (mul-Commutative-Ring R x y) ＝
    mul-Commutative-Ring R
      ( power-Commutative-Ring R n x)
      ( power-Commutative-Ring R n y)
  distributive-power-mul-Commutative-Ring n x y =
    distributive-power-mul-Ring
      ( ring-Commutative-Ring R)
      ( n)
      ( commutative-mul-Commutative-Ring R x y)
```

### `(-x)ⁿ = (-1)ⁿxⁿ`

```agda
module _
  {l : Level} (R : Commutative-Ring l)
  where

  power-neg-Commutative-Ring :
    (n : ℕ) (x : type-Commutative-Ring R) →
    power-Commutative-Ring R n (neg-Commutative-Ring R x) ＝
    mul-Commutative-Ring R
      ( power-Commutative-Ring R n (neg-one-Commutative-Ring R))
      ( power-Commutative-Ring R n x)
  power-neg-Commutative-Ring =
    power-neg-Ring (ring-Commutative-Ring R)

  even-power-neg-Commutative-Ring :
    (n : ℕ) (x : type-Commutative-Ring R) →
    is-even-ℕ n →
    power-Commutative-Ring R n (neg-Commutative-Ring R x) ＝
    power-Commutative-Ring R n x
  even-power-neg-Commutative-Ring =
    even-power-neg-Ring (ring-Commutative-Ring R)

  odd-power-neg-Commutative-Ring :
    (n : ℕ) (x : type-Commutative-Ring R) →
    is-odd-ℕ n →
    power-Commutative-Ring R n (neg-Commutative-Ring R x) ＝
    neg-Commutative-Ring R (power-Commutative-Ring R n x)
  odd-power-neg-Commutative-Ring =
    odd-power-neg-Ring (ring-Commutative-Ring R)
```
