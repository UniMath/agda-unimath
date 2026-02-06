# Binary sum decompositions of positive rational numbers

```agda
module elementary-number-theory.binary-sum-decompositions-positive-rational-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-positive-rational-numbers
open import elementary-number-theory.positive-rational-numbers

open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.universe-levels
```

</details>

## Idea

A
{{#concept "binary sum decomposition" Disambiguation="positive rational number" Agda=binary-sum-decomposition-ℚ⁺}}
of a
[positive rational number](elementary-number-theory.positive-rational-numbers.md)
`x : ℚ⁺` is an ordered pair of positive rationals that sum to `x`.

## Definition

```agda
binary-sum-decomposition-ℚ⁺ : ℚ⁺ → UU lzero
binary-sum-decomposition-ℚ⁺ x =
  Σ ℚ⁺ (λ u → Σ ℚ⁺ (λ v → u +ℚ⁺ v ＝ x))
```

## Properties

### A canonical binary sum decomposition

```agda
split-binary-sum-decomposition-ℚ⁺ :
  (x : ℚ⁺) → binary-sum-decomposition-ℚ⁺ x
split-binary-sum-decomposition-ℚ⁺ = split-ℚ⁺

left-summand-binary-sum-decomposition-ℚ⁺ : ℚ⁺ → ℚ⁺
left-summand-binary-sum-decomposition-ℚ⁺ x =
  pr1 (split-binary-sum-decomposition-ℚ⁺ x)

right-summand-binary-sum-decomposition-ℚ⁺ : ℚ⁺ → ℚ⁺
right-summand-binary-sum-decomposition-ℚ⁺ x =
  pr1 (pr2 (split-binary-sum-decomposition-ℚ⁺ x))

eq-add-binary-sum-decomposition-ℚ⁺ :
  (x : ℚ⁺) →
  left-summand-binary-sum-decomposition-ℚ⁺ x +ℚ⁺
  right-summand-binary-sum-decomposition-ℚ⁺ x ＝ x
eq-add-binary-sum-decomposition-ℚ⁺ x =
  pr2 (pr2 (split-binary-sum-decomposition-ℚ⁺ x))
```
