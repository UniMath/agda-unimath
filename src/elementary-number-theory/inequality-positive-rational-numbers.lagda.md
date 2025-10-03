# Inequality on the positive rational numbers

```agda
module elementary-number-theory.inequality-positive-rational-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.decidable-total-order-rational-numbers
open import elementary-number-theory.inequality-rational-numbers
open import elementary-number-theory.positive-rational-numbers

open import foundation.binary-relations
open import foundation.dependent-pair-types
open import foundation.propositions
open import foundation.universe-levels

open import order-theory.decidable-posets
open import order-theory.decidable-total-orders
open import order-theory.posets
open import order-theory.preorders
open import order-theory.total-orders
```

</details>

## Idea

The
{{#concept "standard ordering" Disambiguation="on the positive rational numbers" Agda=leq-ℚ⁺}}
on the
[positive rational numbers](elementary-number-theory.positive-rational-numbers.md)
is inherited from the
[standard ordering](elementary-number-theory.inequality-rational-numbers.md) on
[rational numbers](elementary-number-theory.rational-numbers.md).

## Definition

```agda
decidable-total-order-ℚ⁺ : Decidable-Total-Order lzero lzero
decidable-total-order-ℚ⁺ =
  decidable-total-order-Decidable-Total-Suborder
    ℚ-Decidable-Total-Order
    is-positive-prop-ℚ

poset-ℚ⁺ : Poset lzero lzero
poset-ℚ⁺ = poset-Decidable-Total-Order decidable-total-order-ℚ⁺

preorder-ℚ⁺ : Preorder lzero lzero
preorder-ℚ⁺ = preorder-Poset poset-ℚ⁺

leq-prop-ℚ⁺ : ℚ⁺ → ℚ⁺ → Prop lzero
leq-prop-ℚ⁺ = leq-prop-Poset poset-ℚ⁺

leq-ℚ⁺ : ℚ⁺ → ℚ⁺ → UU lzero
leq-ℚ⁺ = leq-Poset poset-ℚ⁺

is-prop-leq-ℚ⁺ : (x y : ℚ⁺) → is-prop (leq-ℚ⁺ x y)
is-prop-leq-ℚ⁺ x y = is-prop-type-Prop (leq-prop-ℚ⁺ x y)
```

## Properties

### Inequality on the positive rational numbers is total

```agda
is-total-leq-ℚ⁺ : is-total-Poset poset-ℚ⁺
is-total-leq-ℚ⁺ =
  is-total-poset-Decidable-Total-Order decidable-total-order-ℚ⁺
```

### Inequality on the positive rational numbers is decidable

```agda
is-decidable-leq-ℚ⁺ : is-decidable-leq-Poset poset-ℚ⁺
is-decidable-leq-ℚ⁺ =
  is-decidable-poset-Decidable-Total-Order decidable-total-order-ℚ⁺
```

### Inequality on the positive rational numbers is a partial order

```agda
refl-leq-ℚ⁺ : is-reflexive leq-ℚ⁺
refl-leq-ℚ⁺ = refl-leq-Poset poset-ℚ⁺

transitive-leq-ℚ⁺ : is-transitive leq-ℚ⁺
transitive-leq-ℚ⁺ = transitive-leq-Poset poset-ℚ⁺

antisymmetric-leq-ℚ⁺ : is-antisymmetric leq-ℚ⁺
antisymmetric-leq-ℚ⁺ = antisymmetric-leq-Poset poset-ℚ⁺
```
