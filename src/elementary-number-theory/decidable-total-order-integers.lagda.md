# The decidable total order of integers

```agda
module elementary-number-theory.decidable-total-order-integers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.inequality-integers

open import foundation.dependent-pair-types
open import foundation.propositional-truncations
open import foundation.universe-levels

open import order-theory.decidable-total-orders
open import order-theory.total-orders
```

</details>

## Idea

The type of [integers](elementary-number-theory.integers.md)
[equipped](foundation.structure.md) with its
[standard ordering relation](elementary-number-theory.inequality-integers.md)
forms a [decidable total order](order-theory.decidable-total-orders.md).

## Definition

```agda
is-total-leq-ℤ : is-total-Poset ℤ-Poset
is-total-leq-ℤ x y = unit-trunc-Prop (linear-leq-ℤ x y)

ℤ-Total-Order : Total-Order lzero lzero
pr1 ℤ-Total-Order = ℤ-Poset
pr2 ℤ-Total-Order = is-total-leq-ℤ

ℤ-Decidable-Total-Order : Decidable-Total-Order lzero lzero
pr1 ℤ-Decidable-Total-Order = ℤ-Poset
pr1 (pr2 ℤ-Decidable-Total-Order) = is-total-leq-ℤ
pr2 (pr2 ℤ-Decidable-Total-Order) = is-decidable-leq-ℤ
```
