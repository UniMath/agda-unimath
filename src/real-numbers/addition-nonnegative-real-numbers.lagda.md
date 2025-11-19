# Addition of nonnegative real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.addition-nonnegative-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-nonnegative-rational-numbers
open import elementary-number-theory.addition-positive-rational-numbers
open import elementary-number-theory.nonnegative-rational-numbers
open import elementary-number-theory.positive-and-negative-rational-numbers
open import elementary-number-theory.positive-rational-numbers

open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.disjunction
open import foundation.identity-types
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import real-numbers.addition-real-numbers
open import real-numbers.dedekind-real-numbers
open import real-numbers.inequalities-addition-and-subtraction-real-numbers
open import real-numbers.inequality-nonnegative-real-numbers
open import real-numbers.inequality-real-numbers
open import real-numbers.nonnegative-real-numbers
open import real-numbers.rational-real-numbers
open import real-numbers.strict-inequalities-addition-and-subtraction-real-numbers
open import real-numbers.strict-inequality-nonnegative-real-numbers
```

</details>

## Idea

The [nonnegative](real-numbers.nonnegative-real-numbers.md)
[real numbers](real-numbers.dedekind-real-numbers.md) are closed under
[addition](real-numbers.addition-real-numbers.md).

## Definition

```agda
module _
  {l1 l2 : Level} (x : ℝ⁰⁺ l1) (y : ℝ⁰⁺ l2)
  where

  real-add-ℝ⁰⁺ : ℝ (l1 ⊔ l2)
  real-add-ℝ⁰⁺ = real-ℝ⁰⁺ x +ℝ real-ℝ⁰⁺ y

  abstract
    is-nonnegative-real-add-ℝ⁰⁺ : is-nonnegative-ℝ real-add-ℝ⁰⁺
    is-nonnegative-real-add-ℝ⁰⁺ =
      tr
        ( λ z → leq-ℝ z (real-ℝ⁰⁺ x +ℝ real-ℝ⁰⁺ y))
        ( left-unit-law-add-ℝ zero-ℝ)
        ( preserves-leq-add-ℝ
          ( is-nonnegative-real-ℝ⁰⁺ x)
          ( is-nonnegative-real-ℝ⁰⁺ y))

  add-ℝ⁰⁺ : ℝ⁰⁺ (l1 ⊔ l2)
  add-ℝ⁰⁺ = (real-add-ℝ⁰⁺ , is-nonnegative-real-add-ℝ⁰⁺)

infixl 35 _+ℝ⁰⁺_

_+ℝ⁰⁺_ : {l1 l2 : Level} → ℝ⁰⁺ l1 → ℝ⁰⁺ l2 → ℝ⁰⁺ (l1 ⊔ l2)
_+ℝ⁰⁺_ = add-ℝ⁰⁺
```

## Properties

### Unit laws for addition

```agda
module _
  {l : Level} (x : ℝ⁰⁺ l)
  where

  abstract
    left-unit-law-add-ℝ⁰⁺ : zero-ℝ⁰⁺ +ℝ⁰⁺ x ＝ x
    left-unit-law-add-ℝ⁰⁺ = eq-ℝ⁰⁺ _ _ (left-unit-law-add-ℝ _)

    right-unit-law-add-ℝ⁰⁺ : x +ℝ⁰⁺ zero-ℝ⁰⁺ ＝ x
    right-unit-law-add-ℝ⁰⁺ = eq-ℝ⁰⁺ _ _ (right-unit-law-add-ℝ _)
```

### Addition preserves inequality

```agda
module _
  {l1 l2 l3 l4 : Level} (x : ℝ⁰⁺ l1) (y : ℝ⁰⁺ l2) (z : ℝ⁰⁺ l3) (w : ℝ⁰⁺ l4)
  where

  abstract
    preserves-leq-add-ℝ⁰⁺ :
      leq-ℝ⁰⁺ x y → leq-ℝ⁰⁺ z w → leq-ℝ⁰⁺ (x +ℝ⁰⁺ z) (y +ℝ⁰⁺ w)
    preserves-leq-add-ℝ⁰⁺ = preserves-leq-add-ℝ
```

### The canonical embedding of nonnegative rational numbers to nonnegative real numbers preserves addition

```agda
abstract
  add-nonnegative-real-ℚ⁰⁺ :
    (p q : ℚ⁰⁺) →
    nonnegative-real-ℚ⁰⁺ p +ℝ⁰⁺ nonnegative-real-ℚ⁰⁺ q ＝
    nonnegative-real-ℚ⁰⁺ (p +ℚ⁰⁺ q)
  add-nonnegative-real-ℚ⁰⁺ p q =
    eq-ℝ⁰⁺ _ _ (add-real-ℚ (rational-ℚ⁰⁺ p) (rational-ℚ⁰⁺ q))
```

### The canonical embedding of positive rational numbers to nonnegative real numbers preserves addition

```agda
abstract
  add-nonnegative-real-ℚ⁺ :
    (p q : ℚ⁺) →
    nonnegative-real-ℚ⁺ p +ℝ⁰⁺ nonnegative-real-ℚ⁺ q ＝
    nonnegative-real-ℚ⁺ (p +ℚ⁺ q)
  add-nonnegative-real-ℚ⁺ p q =
    eq-ℝ⁰⁺ _ _ (add-real-ℚ (rational-ℚ⁺ p) (rational-ℚ⁺ q))
```

### Addition preserves strict inequality

```agda
module _
  {l1 l2 l3 l4 : Level} (x : ℝ⁰⁺ l1) (y : ℝ⁰⁺ l2) (z : ℝ⁰⁺ l3) (w : ℝ⁰⁺ l4)
  where

  abstract
    preserves-le-add-ℝ⁰⁺ :
      le-ℝ⁰⁺ x y → le-ℝ⁰⁺ z w → le-ℝ⁰⁺ (x +ℝ⁰⁺ z) (y +ℝ⁰⁺ w)
    preserves-le-add-ℝ⁰⁺ = preserves-le-add-ℝ
```

### Addition with a nonnegative real number is an inflationary map

```agda
abstract
  leq-left-add-real-ℝ⁰⁺ :
    {l1 l2 : Level} → (x : ℝ l1) (d : ℝ⁰⁺ l2) → leq-ℝ x (x +ℝ real-ℝ⁰⁺ d)
  leq-left-add-real-ℝ⁰⁺ x d⁺@(d , pos-d) =
    tr
      ( λ y → leq-ℝ y (x +ℝ d))
      ( right-unit-law-add-ℝ x)
      ( preserves-leq-left-add-ℝ x zero-ℝ d pos-d)

leq-right-add-real-ℝ⁰⁺ :
  {l1 l2 : Level} → (x : ℝ l1) (d : ℝ⁰⁺ l2) → leq-ℝ x (real-ℝ⁰⁺ d +ℝ x)
leq-right-add-real-ℝ⁰⁺ x d =
  tr (leq-ℝ x) (commutative-add-ℝ x (real-ℝ⁰⁺ d)) (leq-left-add-real-ℝ⁰⁺ x d)
```
