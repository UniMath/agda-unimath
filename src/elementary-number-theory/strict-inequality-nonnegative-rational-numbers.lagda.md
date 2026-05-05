# Strict inequality on nonnegative rational numbers

```agda
module elementary-number-theory.strict-inequality-nonnegative-rational-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.inequality-nonnegative-rational-numbers
open import elementary-number-theory.nonnegative-rational-numbers
open import elementary-number-theory.positive-rational-numbers
open import elementary-number-theory.strict-inequality-rational-numbers

open import foundation.dependent-pair-types
open import foundation.propositions
open import foundation.universe-levels
```

</details>

## Idea

The
{{#concept "standard strict ordering" Disambiguation="on the nonegative rational numbers" Agda=le-ℚ⁰⁺}}
on the
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

### Strict inequality on the nonnegative rational numbers is transitive

```agda
abstract
  transitive-le-ℚ⁰⁺ : (p q r : ℚ⁰⁺) → le-ℚ⁰⁺ q r → le-ℚ⁰⁺ p q → le-ℚ⁰⁺ p r
  transitive-le-ℚ⁰⁺ (p , _) (q , _) (r , _) = transitive-le-ℚ p q r
```

### Concatenation laws with inequality

```agda
abstract
  concatenate-le-leq-ℚ⁰⁺ : (p q r : ℚ⁰⁺) → le-ℚ⁰⁺ p q → leq-ℚ⁰⁺ q r → le-ℚ⁰⁺ p r
  concatenate-le-leq-ℚ⁰⁺ (p , _) (q , _) (r , _) = concatenate-le-leq-ℚ p q r

  concatenate-leq-le-ℚ⁰⁺ : (p q r : ℚ⁰⁺) → leq-ℚ⁰⁺ p q → le-ℚ⁰⁺ q r → le-ℚ⁰⁺ p r
  concatenate-leq-le-ℚ⁰⁺ (p , _) (q , _) (r , _) = concatenate-leq-le-ℚ p q r
```
