# Powers of integers

```agda
module elementary-number-theory.powers-integers where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-rings
open import commutative-algebra.powers-of-elements-commutative-rings

open import elementary-number-theory.commutative-ring-of-integers
open import elementary-number-theory.integers
open import elementary-number-theory.multiplication-integers
open import elementary-number-theory.natural-numbers

open import foundation.identity-types
open import foundation.universe-levels

open import ring-theory.powers-of-elements-rings
```

</details>

## Idea

The power operation on the integers is the map `n x ↦ xⁿ`, which is defined by iteratively multiplying `x` with itself `n` times.

## Definition

```agda
power-ℤ : ℕ → ℤ → ℤ
power-ℤ = power-Commutative-Ring ℤ-Commutative-Ring
```

## Properties

### `xⁿ⁺¹ = xⁿx`

```agda
power-succ-ℤ : (n : ℕ) (x : ℤ) → power-ℤ (succ-ℕ n) x ＝ mul-ℤ (power-ℤ n x) x
power-succ-ℤ = power-succ-Commutative-Ring ℤ-Commutative-Ring
```
