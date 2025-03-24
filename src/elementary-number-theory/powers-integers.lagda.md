# Powers of integers

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module elementary-number-theory.powers-integers
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.powers-of-elements-commutative-rings funext univalence truncations

open import elementary-number-theory.integers
open import elementary-number-theory.multiplication-integers funext univalence truncations
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.ring-of-integers funext univalence truncations

open import foundation.identity-types funext
```

</details>

## Idea

The power operation on the integers is the map `n x ↦ xⁿ`, which is defined by
iteratively multiplying `x` with itself `n` times.

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
