# The decidable total order of rational numbers

```agda
module elementary-number-theory.decidable-total-order-rational-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.inequality-rational-numbers

open import foundation.dependent-pair-types
open import foundation.propositional-truncations
open import foundation.universe-levels

open import order-theory.decidable-total-orders
open import order-theory.total-orders
```

</details>

## Idea

The type of [rational numbers](elementary-number-theory.rational-numbers.md)
[equipped](foundation.structure.md) with its
[standard ordering relation](elementary-number-theory.inequality-rational-numbers.md)
forms a [decidable total order](order-theory.decidable-total-orders.md).

## Definition

```agda
is-total-leq-ℚ : is-total-Poset ℚ-Poset
is-total-leq-ℚ x y = unit-trunc-Prop (linear-leq-ℚ x y)

ℚ-Total-Order : Total-Order lzero lzero
pr1 ℚ-Total-Order = ℚ-Poset
pr2 ℚ-Total-Order = is-total-leq-ℚ

ℚ-Decidable-Total-Order : Decidable-Total-Order lzero lzero
pr1 ℚ-Decidable-Total-Order = ℚ-Poset
pr1 (pr2 ℚ-Decidable-Total-Order) = is-total-leq-ℚ
pr2 (pr2 ℚ-Decidable-Total-Order) = is-decidable-leq-ℚ
```
