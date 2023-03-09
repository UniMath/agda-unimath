# Powers of elements in commutative rings

```agda
module commutative-algebra.powers-of-elements-commutative-rings where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-rings

open import elementary-number-theory.natural-numbers

open import foundation.identity-types
open import foundation.universe-levels

open import ring-theory.powers-of-elements-rings
```

</details>

## Idea

The power operation on a commutative ring is the map `n x ↦ xⁿ`, which is defined by iteratively multiplying `x` with itself `n` times.

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
