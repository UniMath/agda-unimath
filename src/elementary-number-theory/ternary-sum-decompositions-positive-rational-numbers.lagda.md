# Ternary sum decompositions of positive rational numbers

```agda
module elementary-number-theory.ternary-sum-decompositions-positive-rational-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-positive-rational-numbers
open import elementary-number-theory.binary-sum-decompositions-positive-rational-numbers
open import elementary-number-theory.positive-rational-numbers

open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.universe-levels
```

</details>

## Idea

A
{{#concept "ternary sum decomposition" Disambiguation="positive rational number" Agda=ternary-sum-decomposition-ℚ⁺}}
of a
[positive rational number](elementary-number-theory.positive-rational-numbers.md)
`x : ℚ⁺` is an ordered triple of positive rationals that sum to `x`.

## Definition

```agda
ternary-sum-decomposition-ℚ⁺ : ℚ⁺ → UU lzero
ternary-sum-decomposition-ℚ⁺ x =
  Σ ℚ⁺ (λ u → Σ ℚ⁺ (λ v → Σ ℚ⁺ (λ w → (u +ℚ⁺ v) +ℚ⁺ w ＝ x)))
```

## Properties

### A canonical ternary sum decomposition

```agda
split-ternary-sum-decomposition-ℚ⁺ :
  (x : ℚ⁺) → ternary-sum-decomposition-ℚ⁺ x
split-ternary-sum-decomposition-ℚ⁺ x =
  let
    u = left-summand-binary-sum-decomposition-ℚ⁺ x
    r = right-summand-binary-sum-decomposition-ℚ⁺ x
    v = left-summand-binary-sum-decomposition-ℚ⁺ r
    w = right-summand-binary-sum-decomposition-ℚ⁺ r
  in
    ( u , v , w ,
      ( associative-add-ℚ⁺ u v w) ∙
      ( ap (u +ℚ⁺_) (eq-add-binary-sum-decomposition-ℚ⁺ r)) ∙
      ( eq-add-binary-sum-decomposition-ℚ⁺ x))

left-summand-ternary-sum-decomposition-ℚ⁺ : ℚ⁺ → ℚ⁺
left-summand-ternary-sum-decomposition-ℚ⁺ x =
  pr1 (split-ternary-sum-decomposition-ℚ⁺ x)

middle-summand-ternary-sum-decomposition-ℚ⁺ : ℚ⁺ → ℚ⁺
middle-summand-ternary-sum-decomposition-ℚ⁺ x =
  pr1 (pr2 (split-ternary-sum-decomposition-ℚ⁺ x))

right-summand-ternary-sum-decomposition-ℚ⁺ : ℚ⁺ → ℚ⁺
right-summand-ternary-sum-decomposition-ℚ⁺ x =
  pr1 (pr2 (pr2 (split-ternary-sum-decomposition-ℚ⁺ x)))

eq-add-ternary-sum-decomposition-ℚ⁺ :
  (x : ℚ⁺) →
  ( ( left-summand-ternary-sum-decomposition-ℚ⁺ x +ℚ⁺
      middle-summand-ternary-sum-decomposition-ℚ⁺ x) +ℚ⁺
      right-summand-ternary-sum-decomposition-ℚ⁺ x) ＝
  ( x)
eq-add-ternary-sum-decomposition-ℚ⁺ x =
  pr2 (pr2 (pr2 (split-ternary-sum-decomposition-ℚ⁺ x)))
```
