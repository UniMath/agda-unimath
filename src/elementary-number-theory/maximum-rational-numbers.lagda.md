# Maximum on the rational numbers

```agda
module elementary-number-theory.maximum-rational-numbers where
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

We define the operation of maximum
([least upper bound](order-theory.least-upper-bounds-posets.md)) for the
[rational numbers](elementary-number-theory.rational-numbers.md).

## Definition

```agda
max-ℚ : ℚ → ℚ → ℚ
max-ℚ = max-Decidable-Total-Order ℚ-Decidable-Total-Order
```

## Properties

### Associativity of `max-ℚ`

```agda
associative-max-ℚ : (x y z : ℚ) → max-ℚ (max-ℚ x y) z ＝ max-ℚ x (max-ℚ y z)
associative-max-ℚ =
  associative-max-Decidable-Total-Order ℚ-Decidable-Total-Order
```

### Commutativity of `max-ℚ`

```agda
commutative-max-ℚ : (x y : ℚ) → max-ℚ x y ＝ max-ℚ y x
commutative-max-ℚ =
  commutative-max-Decidable-Total-Order ℚ-Decidable-Total-Order
```

### `max-ℚ` is idempotent

```agda
idempotent-max-ℚ : (x : ℚ) → max-ℚ x x ＝ x
idempotent-max-ℚ =
  idempotent-max-Decidable-Total-Order ℚ-Decidable-Total-Order
```
