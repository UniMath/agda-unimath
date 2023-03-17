# Powers of elements in commutative semirings

```agda
module commutative-algebra.powers-of-elements-commutative-semirings where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-semirings

open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.identity-types
open import foundation.universe-levels

open import ring-theory.powers-of-elements-semirings
```

</details>

## Idea

The power operation on a commutative semiring is the map `n x ↦ xⁿ`, which is
defined by iteratively multiplying `x` with itself `n` times.

## Definition

```agda
power-Commutative-Semiring :
  {l : Level} (R : Commutative-Semiring l) →
  ℕ → type-Commutative-Semiring R → type-Commutative-Semiring R
power-Commutative-Semiring R = power-Semiring (semiring-Commutative-Semiring R)
```

## Properties

### `xⁿ⁺¹ = xⁿx`

```agda
module _
  {l : Level} (R : Commutative-Semiring l)
  where

  power-succ-Commutative-Semiring :
    (n : ℕ) (x : type-Commutative-Semiring R) →
    power-Commutative-Semiring R (succ-ℕ n) x ＝
    mul-Commutative-Semiring R (power-Commutative-Semiring R n x) x
  power-succ-Commutative-Semiring =
    power-succ-Semiring (semiring-Commutative-Semiring R)
```

### Powers by sums of natural numbers are products of powers

```agda
module _
  {l : Level} (R : Commutative-Semiring l)
  where

  power-add-Commutative-Semiring :
    (m n : ℕ) {x : type-Commutative-Semiring R} →
    power-Commutative-Semiring R (add-ℕ m n) x ＝
    mul-Commutative-Semiring R
      ( power-Commutative-Semiring R m x)
      ( power-Commutative-Semiring R n x)
  power-add-Commutative-Semiring =
    power-add-Semiring (semiring-Commutative-Semiring R)
```

### If `x` commutes with `y`, then powers distribute over the product of `x` and `y`.

```agda
module _
  {l : Level} (R : Commutative-Semiring l)
  where
  
  distributive-power-mul-Commutative-Semiring :
    (n : ℕ) (x y : type-Commutative-Semiring R) →
    power-Commutative-Semiring R n (mul-Commutative-Semiring R x y) ＝
    mul-Commutative-Semiring R
      ( power-Commutative-Semiring R n x)
      ( power-Commutative-Semiring R n y)
  distributive-power-mul-Commutative-Semiring n x y =
    distributive-power-mul-Semiring
      ( semiring-Commutative-Semiring R)
      ( n)
      ( commutative-mul-Commutative-Semiring R x y)
```
