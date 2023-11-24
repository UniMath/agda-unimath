# The decidable total order of a standard finite type

```agda
module elementary-number-theory.decidable-total-order-standard-finite-types where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.inequality-standard-finite-types
open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.propositional-truncations
open import foundation.universe-levels

open import order-theory.decidable-total-orders
open import order-theory.total-orders
```

</details>

## Idea

The [standard finite type](univalent-combinatorics.standard-finite-types.md) of
order `k` [equipped](foundation.structure.md) with its
[standard ordering relation](elementary-number-theory.inequality-standard-finite-types.md)
forms a [decidable total order](order-theory.decidable-total-orders.md).

## Definition

```agda
is-total-leq-Fin : (k : ℕ) → is-total-Poset (Fin-Poset k)
is-total-leq-Fin k n m = unit-trunc-Prop (linear-leq-Fin k n m)

Fin-Total-Order : ℕ → Total-Order lzero lzero
pr1 (Fin-Total-Order k) = Fin-Poset k
pr2 (Fin-Total-Order k) = is-total-leq-Fin k

Fin-Decidable-Total-Order : ℕ → Decidable-Total-Order lzero lzero
pr1 (Fin-Decidable-Total-Order k) = Fin-Poset k
pr1 (pr2 (Fin-Decidable-Total-Order k)) = is-total-leq-Fin k
pr2 (pr2 (Fin-Decidable-Total-Order k)) = is-decidable-leq-Fin k
```
