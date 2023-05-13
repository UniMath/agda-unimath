# Natural numbers are a total decidable poset

```agda
module elementary-number-theory.decidable-total-order-natural-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.inequality-natural-numbers

open import foundation.dependent-pair-types
open import foundation.propositional-truncations
open import foundation.universe-levels

open import order-theory.decidable-total-orders
```

</details>

## Idea

The type of natural numbers equipped with its standard ordering relation forms a
total order.

## Definition

```agda
ℕ-Decidable-Total-Order :
  Decidable-Total-Order lzero lzero
pr1 ℕ-Decidable-Total-Order = ℕ-Poset
pr1 (pr2 ℕ-Decidable-Total-Order) n m = unit-trunc-Prop (linear-leq-ℕ n m)
pr2 (pr2 ℕ-Decidable-Total-Order) = is-decidable-leq-ℕ
```
