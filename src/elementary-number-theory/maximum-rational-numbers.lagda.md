# Maximum on the rational numbers

```agda
module elementary-number-theory.maximum-rational-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.decidable-total-order-rational-numbers
open import elementary-number-theory.inequality-rational-numbers
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.strict-inequality-rational-numbers

open import foundation.action-on-identifications-binary-functions
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.transport-along-identifications

open import order-theory.decidable-total-orders
```

</details>

## Idea

The {{#concept "maximum" Disambiguation="of rational numbers" Agda=max-ℚ}} of
two [rational numbers](elementary-number-theory.rational-numbers.md) is the
[greatest](elementary-number-theory.inequality-rational-numbers.md) rational
number of the two. This is the
[binary least upper bound](order-theory.least-upper-bounds-posets.md) in the
[total order of rational numbers](elementary-number-theory.decidable-total-order-rational-numbers.md).

## Definition

```agda
max-ℚ : ℚ → ℚ → ℚ
max-ℚ = max-Decidable-Total-Order ℚ-Decidable-Total-Order

ap-max-ℚ :
  {p p' : ℚ} → (p ＝ p') → {q q' : ℚ} → (q ＝ q') → max-ℚ p q ＝ max-ℚ p' q'
ap-max-ℚ = ap-binary max-ℚ
```

## Properties

### Associativity of the maximum operation

```agda
abstract
  associative-max-ℚ : (x y z : ℚ) → max-ℚ (max-ℚ x y) z ＝ max-ℚ x (max-ℚ y z)
  associative-max-ℚ =
    associative-max-Decidable-Total-Order ℚ-Decidable-Total-Order
```

### Commutativity of the maximum operation

```agda
abstract
  commutative-max-ℚ : (x y : ℚ) → max-ℚ x y ＝ max-ℚ y x
  commutative-max-ℚ =
    commutative-max-Decidable-Total-Order ℚ-Decidable-Total-Order
```

### The maximum operation is idempotent

```agda
abstract
  idempotent-max-ℚ : (x : ℚ) → max-ℚ x x ＝ x
  idempotent-max-ℚ =
    idempotent-max-Decidable-Total-Order ℚ-Decidable-Total-Order
```

### The maximum is an upper bound

```agda
abstract
  leq-left-max-ℚ : (x y : ℚ) → x ≤-ℚ max-ℚ x y
  leq-left-max-ℚ = leq-left-max-Decidable-Total-Order ℚ-Decidable-Total-Order

  leq-right-max-ℚ : (x y : ℚ) → y ≤-ℚ max-ℚ x y
  leq-right-max-ℚ = leq-right-max-Decidable-Total-Order ℚ-Decidable-Total-Order
```

### If `a` is less than or equal to `b`, then the maximum of `a` and `b` is `b`

```agda
abstract
  left-leq-right-max-ℚ : (x y : ℚ) → leq-ℚ x y → max-ℚ x y ＝ y
  left-leq-right-max-ℚ =
    left-leq-right-max-Decidable-Total-Order ℚ-Decidable-Total-Order

  right-leq-left-max-ℚ : (x y : ℚ) → leq-ℚ y x → max-ℚ x y ＝ x
  right-leq-left-max-ℚ =
    right-leq-left-max-Decidable-Total-Order ℚ-Decidable-Total-Order
```

### If both `x` and `y` are less than `z`, so is their maximum

```agda
abstract
  le-max-le-both-ℚ : (z x y : ℚ) → le-ℚ x z → le-ℚ y z → le-ℚ (max-ℚ x y) z
  le-max-le-both-ℚ z x y x<z y<z with decide-le-leq-ℚ x y
  ... | inl x<y =
    inv-tr
      ( λ w → le-ℚ w z)
      ( left-leq-right-max-Decidable-Total-Order
        ( ℚ-Decidable-Total-Order)
        ( x)
        ( y)
        ( leq-le-ℚ {x} {y} x<y))
      ( y<z)
  ... | inr y≤x =
    inv-tr
      ( λ w → le-ℚ w z)
      ( right-leq-left-max-Decidable-Total-Order ℚ-Decidable-Total-Order
        ( x)
        ( y)
        ( y≤x))
      ( x<z)

  leq-max-leq-both-ℚ : (z x y : ℚ) → leq-ℚ x z → leq-ℚ y z → leq-ℚ (max-ℚ x y) z
  leq-max-leq-both-ℚ z x y x≤z y≤z =
    forward-implication
      ( max-is-least-binary-upper-bound-Decidable-Total-Order
        ( ℚ-Decidable-Total-Order)
        ( x)
        ( y)
        ( z))
      ( x≤z , y≤z)
```

### If `a ≤ b` and `c ≤ d`, then `max a c ≤ max b d`

```agda
abstract
  max-leq-leq-ℚ :
    (a b c d : ℚ) → leq-ℚ a b → leq-ℚ c d → leq-ℚ (max-ℚ a c) (max-ℚ b d)
  max-leq-leq-ℚ = max-leq-leq-Decidable-Total-Order ℚ-Decidable-Total-Order
```
