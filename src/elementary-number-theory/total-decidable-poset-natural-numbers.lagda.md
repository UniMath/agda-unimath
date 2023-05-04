# Natural numbers are a total decidable poset

```agda
module elementary-number-theory.total-decidable-poset-natural-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.inequality-natural-numbers

open import foundation.dependent-pair-types
open import foundation.universe-levels
open import foundation.propositional-truncations

open import order-theory.total-decidable-posets
```

</details>

## Idea

In these file, we show defined the total decidable poset of natural numbers.

## Definition

```agda
ℕ-total-decidable-Poset :
  total-decidable-Poset lzero lzero
pr1 ℕ-total-decidable-Poset = ℕ-Poset
pr1 (pr2 ℕ-total-decidable-Poset) n m = unit-trunc-Prop (linear-leq-ℕ n m)
pr2 (pr2 ℕ-total-decidable-Poset) = is-decidable-leq-ℕ

```
