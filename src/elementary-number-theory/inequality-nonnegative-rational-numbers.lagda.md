# Inequality on the nonnegative rational numbers

```agda
module elementary-number-theory.inequality-nonnegative-rational-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.decidable-total-order-rational-numbers
open import elementary-number-theory.inequality-rational-numbers
open import elementary-number-theory.nonnegative-rational-numbers

open import foundation.dependent-pair-types
open import foundation.propositions
open import foundation.universe-levels

open import order-theory.decidable-total-orders
```

</details>

## Idea

The
{{#concept "standard ordering" Disambiguation="on the nonnegative rational numbers" Agda=leq-ℚ⁰⁺}}
on the
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

## Properties

### The decidable total order of nonnegative rational numbers

```agda
decidable-total-order-ℚ⁰⁺ : Decidable-Total-Order lzero lzero
decidable-total-order-ℚ⁰⁺ =
  decidable-total-order-Decidable-Total-Suborder
    ℚ-Decidable-Total-Order
    is-nonnegative-prop-ℚ
```
