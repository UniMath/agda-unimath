# Strict inequality on nonnegative rational numbers

```agda
module elementary-number-theory.strict-inequality-nonnegative-rational-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.nonnegative-rational-numbers
open import elementary-number-theory.positive-rational-numbers
open import elementary-number-theory.strict-inequality-rational-numbers

open import foundation.dependent-pair-types
open import foundation.propositions
open import foundation.universe-levels
```

</details>

## Idea

The {{#concept "standard strict ordering" Disambiguation="on the nonegative rational numbers" Agda=le-ℚ⁰⁺}} on the
[nonnegative rational numbers](elementary-number-theory.nonnegative-rational-numbers.md)
is inherited from the
[standard strict ordering](elementary-number-theory.strict-inequality-rational-numbers.md)
on [rational numbers](elementary-number-theory.rational-numbers.md).

## Definition

```agda
le-prop-ℚ⁰⁺ : (p q : ℚ⁰⁺) → Prop lzero
le-prop-ℚ⁰⁺ p q = le-ℚ-Prop (rational-ℚ⁰⁺ p) (rational-ℚ⁰⁺ q)

le-ℚ⁰⁺ : (p q : ℚ⁰⁺) → UU lzero
le-ℚ⁰⁺ p q = type-Prop (le-prop-ℚ⁰⁺ p q)
```

## Properties

### Zero is less than positive rational numbers as nonnegative rational numbers

```agda
abstract
  le-zero-nonnegative-ℚ⁰⁺ : (q : ℚ⁺) → le-ℚ⁰⁺ zero-ℚ⁰⁺ (nonnegative-ℚ⁺ q)
  le-zero-nonnegative-ℚ⁰⁺ (q , pos-q) = le-zero-is-positive-ℚ q pos-q
```
