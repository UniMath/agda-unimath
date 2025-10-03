# The maximum of positive rational numbers

```agda
module elementary-number-theory.maximum-positive-rational-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.inequality-positive-rational-numbers
open import elementary-number-theory.positive-rational-numbers

open import foundation.identity-types

open import order-theory.decidable-total-orders
```

</details>

## Idea

The maximum of two
[positive rational numbers](elementary-number-theory.positive-rational-numbers.md)
is the
[greatest](elementary-number-theory.inequality-positive-rational-numbers.md)
rational number of the two.

## Definition

```agda
max-ℚ⁺ : ℚ⁺ → ℚ⁺ → ℚ⁺
max-ℚ⁺ = max-Decidable-Total-Order decidable-total-order-ℚ⁺
```

## Properties

### The binary maximum is associative

```agda
abstract
  associative-max-ℚ⁺ :
    (x y z : ℚ⁺) → max-ℚ⁺ (max-ℚ⁺ x y) z ＝ max-ℚ⁺ x (max-ℚ⁺ y z)
  associative-max-ℚ⁺ =
    associative-max-Decidable-Total-Order decidable-total-order-ℚ⁺
```

### The binary maximum is commutative

```agda
abstract
  commutative-max-ℚ⁺ : (x y : ℚ⁺) → max-ℚ⁺ x y ＝ max-ℚ⁺ y x
  commutative-max-ℚ⁺ =
    commutative-max-Decidable-Total-Order decidable-total-order-ℚ⁺
```

### The binary maximum is idempotent

```agda
abstract
  idempotent-max-ℚ⁺ : (x : ℚ⁺) → max-ℚ⁺ x x ＝ x
  idempotent-max-ℚ⁺ =
    idempotent-max-Decidable-Total-Order decidable-total-order-ℚ⁺
```

### The binary maximum is an upper bound

```agda
abstract
  leq-left-max-ℚ⁺ : (x y : ℚ⁺) → leq-ℚ⁺ x (max-ℚ⁺ x y)
  leq-left-max-ℚ⁺ = leq-left-max-Decidable-Total-Order decidable-total-order-ℚ⁺

  leq-right-max-ℚ⁺ : (x y : ℚ⁺) → leq-ℚ⁺ y (max-ℚ⁺ x y)
  leq-right-max-ℚ⁺ =
    leq-right-max-Decidable-Total-Order decidable-total-order-ℚ⁺
```
