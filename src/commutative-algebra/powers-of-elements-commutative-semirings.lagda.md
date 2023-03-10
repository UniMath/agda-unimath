# Powers of elements in commutative semirings

```agda
module commutative-algebra.powers-of-elements-commutative-semirings where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-semirings

open import elementary-number-theory.natural-numbers

open import foundation.identity-types
open import foundation.universe-levels

open import ring-theory.powers-of-elements-semirings
```

</details>

## Idea

The power operation on a commutative semiring is the map `n x ↦ xⁿ`, which is defined by iteratively multiplying `x` with itself `n` times.

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
