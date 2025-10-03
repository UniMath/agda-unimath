# Inequality on the nonnegative rational numbers

```agda
module elementary-number-theory.inequality-nonnegative-rational-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.inequality-rational-numbers
open import elementary-number-theory.nonnegative-rational-numbers

open import foundation.dependent-pair-types
open import foundation.propositions
open import foundation.universe-levels
```

</details>

## Idea

The standard ordering on the
[nonnegative rational numbers](elementary-number-theory.nonnegative-rational-numbers.md)
is inherited from the
[standard ordering](elementary-number-theory.inequality-rational-numbers.md) on
[rational numbers](elementary-number-theory.rational-numbers.md).

## Definition

```agda
leq-prop-ℚ⁰⁺ : ℚ⁰⁺ → ℚ⁰⁺ → Prop lzero
leq-prop-ℚ⁰⁺ (p , _) (q , _) = leq-ℚ-Prop p q

leq-ℚ⁰⁺ : ℚ⁰⁺ → ℚ⁰⁺ → UU lzero
leq-ℚ⁰⁺ (p , _) (q , _) = leq-ℚ p q
```
