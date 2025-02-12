# Minimum on the rational numbers

```agda
module elementary-number-theory.minimum-rational-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.decidable-total-order-rational-numbers
open import elementary-number-theory.inequality-rational-numbers
open import elementary-number-theory.rational-numbers

open import foundation.identity-types

open import order-theory.decidable-total-orders
```

</details>

## Idea

We define the operation of minimum (greatest lower bound) for the rational
numbers.

## Definition

```agda
min-ℚ : ℚ → ℚ → ℚ
min-ℚ = min-Decidable-Total-Order ℚ-Decidable-Total-Order
```

## Properties

### Associativity of `min-ℚ`

```agda

```

### Commutativity of `min-ℚ`

```agda

```

### `min-ℚ` is idempotent

```agda
idempotent-min-ℚ : (x : ℚ) → min-ℚ x x ＝ x
```
