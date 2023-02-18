#  Powers of elements in rings

```agda
module ring-theory.powers-of-elements-rings where

open import elementary-number-theory.natural-numbers

open import foundation.identity-types
open import foundation.universe-levels

open import ring-theory.rings
```

## Definition

```agda
power-Ring : {l : Level} (R : Ring l) → ℕ → type-Ring R → type-Ring R
power-Ring R zero-ℕ x = one-Ring R
power-Ring R (succ-ℕ zero-ℕ) x = x
power-Ring R (succ-ℕ (succ-ℕ n)) x = mul-Ring R (power-Ring R (succ-ℕ n) x) x
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
  power-succ-Ring zero-ℕ x = inv (left-unit-law-mul-Ring R x)
  power-succ-Ring (succ-ℕ n) x = refl
```
