# Minimum on the rational numbers

```agda
module elementary-number-theory.minimum-rational-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.decidable-total-order-rational-numbers
open import elementary-number-theory.inequality-rational-numbers
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.strict-inequality-rational-numbers

open import foundation.action-on-identifications-binary-functions
open import foundation.coproduct-types
open import foundation.identity-types
open import foundation.transport-along-identifications

open import order-theory.decidable-total-orders
```

</details>

## Idea

The {{#concept "minimum" Disambiguation="of rational numbers" Agda=min-ℚ}} of
two [rational numbers](elementary-number-theory.rational-numbers.md) is the
[smallest](elementary-number-theory.inequality-rational-numbers.md) rational
number of the two. This is the
[binary greatest lower bound](order-theory.greatest-lower-bounds-posets.md) in
the
[total order of rational numbers](elementary-number-theory.decidable-total-order-rational-numbers.md).

## Definition

```agda
min-ℚ : ℚ → ℚ → ℚ
min-ℚ = min-Decidable-Total-Order ℚ-Decidable-Total-Order

ap-min-ℚ :
  {p p' : ℚ} → (p ＝ p') → {q q' : ℚ} → (q ＝ q') → min-ℚ p q ＝ min-ℚ p' q'
ap-min-ℚ = ap-binary min-ℚ
```

## Properties

### Associativity of the minimum operation

```agda
abstract
  associative-min-ℚ : (x y z : ℚ) → min-ℚ (min-ℚ x y) z ＝ min-ℚ x (min-ℚ y z)
  associative-min-ℚ =
    associative-min-Decidable-Total-Order ℚ-Decidable-Total-Order
```

### Commutativity of the minimum operation

```agda
abstract
  commutative-min-ℚ : (x y : ℚ) → min-ℚ x y ＝ min-ℚ y x
  commutative-min-ℚ =
    commutative-min-Decidable-Total-Order ℚ-Decidable-Total-Order
```

### The minimum operation is idempotent

```agda
abstract
  idempotent-min-ℚ : (x : ℚ) → min-ℚ x x ＝ x
  idempotent-min-ℚ =
    idempotent-min-Decidable-Total-Order ℚ-Decidable-Total-Order
```

### The minimum is a lower bound

```agda
abstract
  leq-left-min-ℚ : (x y : ℚ) → min-ℚ x y ≤-ℚ x
  leq-left-min-ℚ = leq-left-min-Decidable-Total-Order ℚ-Decidable-Total-Order

  leq-right-min-ℚ : (x y : ℚ) → min-ℚ x y ≤-ℚ y
  leq-right-min-ℚ = leq-right-min-Decidable-Total-Order ℚ-Decidable-Total-Order
```

### If `a` is less than or equal to `b`, then the minimum of `a` and `b` is `a`

```agda
abstract
  left-leq-right-min-ℚ : (x y : ℚ) → leq-ℚ x y → min-ℚ x y ＝ x
  left-leq-right-min-ℚ =
    left-leq-right-min-Decidable-Total-Order ℚ-Decidable-Total-Order

  right-leq-left-min-ℚ : (x y : ℚ) → leq-ℚ y x → min-ℚ x y ＝ y
  right-leq-left-min-ℚ =
    right-leq-left-min-Decidable-Total-Order ℚ-Decidable-Total-Order
```

### If `z` is less than both `x` and `y`, it is less than their minimum

```agda
abstract
  le-min-le-both-ℚ : (z x y : ℚ) → le-ℚ z x → le-ℚ z y → le-ℚ z (min-ℚ x y)
  le-min-le-both-ℚ z x y z<x z<y with decide-le-leq-ℚ x y
  ... | inl x<y =
    inv-tr
      ( le-ℚ z)
      ( left-leq-right-min-Decidable-Total-Order
        ( ℚ-Decidable-Total-Order)
        ( x)
        ( y)
        ( leq-le-ℚ {x} {y} x<y))
      ( z<x)
  ... | inr y≤x =
    inv-tr
      ( le-ℚ z)
      ( right-leq-left-min-Decidable-Total-Order
          ℚ-Decidable-Total-Order x y y≤x)
      ( z<y)
```

### If `a ≤ b` and `c ≤ d`, then `min a c ≤ min b d`

```agda
abstract
  min-leq-leq-ℚ :
    (a b c d : ℚ) → leq-ℚ a b → leq-ℚ c d → leq-ℚ (min-ℚ a c) (min-ℚ b d)
  min-leq-leq-ℚ = min-leq-leq-Decidable-Total-Order ℚ-Decidable-Total-Order
```
