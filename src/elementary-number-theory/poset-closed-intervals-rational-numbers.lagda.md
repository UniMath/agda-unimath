# The poset of closed intervals of rational numbers

```agda
module elementary-number-theory.poset-closed-intervals-rational-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.closed-intervals-rational-numbers
open import elementary-number-theory.decidable-total-order-rational-numbers

open import foundation.binary-relations
open import foundation.universe-levels

open import order-theory.closed-intervals-total-orders
open import order-theory.poset-closed-intervals-total-orders
open import order-theory.posets
open import order-theory.preorders
```

</details>

## Idea

The
[closed intervals](elementary-number-theory.closed-intervals-rational-numbers.md)
of [rational numbers](elementary-number-theory.rational-numbers.md) form a
[poset](order-theory.posets.md) under the containment relation.

## Definition

```agda
leq-prop-closed-interval-ℚ : Relation-Prop lzero closed-interval-ℚ
leq-prop-closed-interval-ℚ =
  leq-prop-closed-interval-Total-Order ℚ-Total-Order

leq-closed-interval-ℚ : Relation lzero closed-interval-ℚ
leq-closed-interval-ℚ = leq-closed-interval-Total-Order ℚ-Total-Order
```

## Properties

### The containment relation is a partial order

```agda
abstract
  refl-leq-closed-interval-ℚ : is-reflexive leq-closed-interval-ℚ
  refl-leq-closed-interval-ℚ =
    refl-leq-closed-interval-Total-Order ℚ-Total-Order

  transitive-leq-closed-interval-ℚ : is-transitive leq-closed-interval-ℚ
  transitive-leq-closed-interval-ℚ =
    transitive-leq-closed-interval-Total-Order ℚ-Total-Order

  antisymmetric-leq-closed-interval-ℚ : is-antisymmetric leq-closed-interval-ℚ
  antisymmetric-leq-closed-interval-ℚ =
    antisymmetric-leq-closed-interval-Total-Order ℚ-Total-Order

poset-closed-interval-ℚ : Poset lzero lzero
poset-closed-interval-ℚ = poset-closed-interval-Total-Order ℚ-Total-Order
```
