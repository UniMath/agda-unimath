# Powers of integers

```agda
module elementary-number-theory.powers-integers where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.powers-of-elements-commutative-rings

open import elementary-number-theory.integers
open import elementary-number-theory.multiplication-integers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.ring-of-integers

open import foundation.identity-types
```

</details>

## Idea

The
{{#concept "power operation" WDID=Q33456 WD="exponentiation" Disambiguation="on the integers" Agda=power-ℤ}}
on the [integers](elementary-number-theory.integers.md) is the map `n x ↦ xⁿ`,
which is defined by iteratively multiplying `x` with itself `n` times.

## Definition

```agda
power-ℤ : ℕ → ℤ → ℤ
power-ℤ = power-Commutative-Ring ℤ-Commutative-Ring
```

## Properties

### `xⁿ⁺¹ = xⁿx`

```agda
power-succ-ℤ : (n : ℕ) (x : ℤ) → power-ℤ (succ-ℕ n) x ＝ (power-ℤ n x) *ℤ x
power-succ-ℤ = power-succ-Commutative-Ring ℤ-Commutative-Ring
```
