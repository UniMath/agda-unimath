# Multiplication by negative rational numbers

```agda
{-# OPTIONS --lossy-unification #-}

module elementary-number-theory.multiplication-negative-rational-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.inequality-rational-numbers
open import elementary-number-theory.multiplication-positive-rational-numbers
open import elementary-number-theory.multiplication-rational-numbers
open import elementary-number-theory.multiplicative-group-of-positive-rational-numbers
open import elementary-number-theory.negative-rational-numbers
open import elementary-number-theory.positive-and-negative-rational-numbers
open import elementary-number-theory.positive-rational-numbers
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.strict-inequality-rational-numbers

open import foundation.action-on-identifications-functions
open import foundation.binary-transport
open import foundation.identity-types
open import foundation.transport-along-identifications
```

</details>

## Idea

The product of two
[negative rational numbers](elementary-number-theory.negative-rational-numbers.md)
is their [product](elementary-number-theory.multiplication-rational-numbers.md)
as [rational numbers](elementary-number-theory.rational-numbers.md), and is
[positive](elementary-number-theory.positive-rational-numbers.md).

## Properties

### The product of two negative rational numbers is positive

```agda
opaque
  unfolding is-negative-ℚ

  is-positive-mul-negative-ℚ :
    {x y : ℚ} → is-negative-ℚ x → is-negative-ℚ y → is-positive-ℚ (x *ℚ y)
  is-positive-mul-negative-ℚ {x} {y} P Q =
    tr
      ( is-positive-ℚ)
      ( negative-law-mul-ℚ x y)
      ( is-positive-mul-ℚ P Q)
```

### Multiplication by a negative rational number reverses inequality

```agda
module _
  (p : ℚ⁻)
  (q r : ℚ)
  (H : leq-ℚ q r)
  where

  abstract
    reverses-leq-right-mul-ℚ⁻ : leq-ℚ (r *ℚ rational-ℚ⁻ p) (q *ℚ rational-ℚ⁻ p)
    reverses-leq-right-mul-ℚ⁻ =
      binary-tr
        ( leq-ℚ)
        ( negative-law-mul-ℚ r (rational-ℚ⁻ p))
        ( negative-law-mul-ℚ q (rational-ℚ⁻ p))
        ( preserves-leq-right-mul-ℚ⁺
          ( neg-ℚ⁻ p)
          ( neg-ℚ r)
          ( neg-ℚ q)
          ( neg-leq-ℚ H))
```

### Multiplication by a negative rational number reverses strict inequality

```agda
module _
  (p : ℚ⁻)
  (q r : ℚ)
  (H : le-ℚ q r)
  where

  abstract
    reverses-le-right-mul-ℚ⁻ : le-ℚ (r *ℚ rational-ℚ⁻ p) (q *ℚ rational-ℚ⁻ p)
    reverses-le-right-mul-ℚ⁻ =
      binary-tr
        ( le-ℚ)
        ( negative-law-mul-ℚ r (rational-ℚ⁻ p))
        ( negative-law-mul-ℚ q (rational-ℚ⁻ p))
        ( preserves-le-right-mul-ℚ⁺
          ( neg-ℚ⁻ p)
          ( neg-ℚ r)
          ( neg-ℚ q)
          ( neg-le-ℚ H))

    reverses-le-left-mul-ℚ⁻ : le-ℚ (rational-ℚ⁻ p *ℚ r) (rational-ℚ⁻ p *ℚ q)
    reverses-le-left-mul-ℚ⁻ =
      binary-tr
        ( le-ℚ)
        ( commutative-mul-ℚ _ _)
        ( commutative-mul-ℚ _ _)
        ( reverses-le-right-mul-ℚ⁻)
```

### The negative rational numbers are invertible elements of the multiplicative monoid of rational numbers

```agda
opaque
  inv-ℚ⁻ : ℚ⁻ → ℚ⁻
  inv-ℚ⁻ q = neg-ℚ⁺ (inv-ℚ⁺ (neg-ℚ⁻ q))

  left-inverse-law-mul-ℚ⁻ :
    (q : ℚ⁻) → rational-ℚ⁻ (inv-ℚ⁻ q) *ℚ rational-ℚ⁻ q ＝ one-ℚ
  left-inverse-law-mul-ℚ⁻ q =
    inv (swap-neg-mul-ℚ _ _) ∙
    ap rational-ℚ⁺ (left-inverse-law-mul-ℚ⁺ (neg-ℚ⁻ q))

  right-inverse-law-mul-ℚ⁻ :
    (q : ℚ⁻) → rational-ℚ⁻ q *ℚ rational-ℚ⁻ (inv-ℚ⁻ q) ＝ one-ℚ
  right-inverse-law-mul-ℚ⁻ q =
    swap-neg-mul-ℚ _ _ ∙
    ap rational-ℚ⁺ (right-inverse-law-mul-ℚ⁺ (neg-ℚ⁻ q))
```

### Inversion reverses inequality on negative rational numbers

```agda
opaque
  unfolding inv-ℚ⁻

  reverses-leq-inv-ℚ⁻ :
    (p q : ℚ⁻) → leq-ℚ⁻ p q → leq-ℚ⁻ (inv-ℚ⁻ q) (inv-ℚ⁻ p)
  reverses-leq-inv-ℚ⁻ p q p≤q =
    neg-leq-ℚ
      ( inv-leq-ℚ⁺
        ( neg-ℚ⁻ q)
        ( neg-ℚ⁻ p)
        ( neg-leq-ℚ p≤q))
```

### Inversion reverses strict inequality on negative rational numbers

```agda
opaque
  unfolding inv-ℚ⁻

  reverses-le-inv-ℚ⁻ :
    (p q : ℚ⁻) → le-ℚ⁻ p q → le-ℚ⁻ (inv-ℚ⁻ q) (inv-ℚ⁻ p)
  reverses-le-inv-ℚ⁻ p q p<q =
    neg-le-ℚ
      ( inv-le-ℚ⁺
        ( neg-ℚ⁻ q)
        ( neg-ℚ⁻ p)
        ( neg-le-ℚ p<q))
```
