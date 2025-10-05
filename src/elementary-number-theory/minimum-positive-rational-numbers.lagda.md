# The minimum of positive rational numbers

```agda
module elementary-number-theory.minimum-positive-rational-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.inequality-positive-rational-numbers
open import elementary-number-theory.minimum-rational-numbers
open import elementary-number-theory.positive-rational-numbers
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.strict-inequality-positive-rational-numbers
open import elementary-number-theory.strict-inequality-rational-numbers

open import foundation.dependent-pair-types
open import foundation.identity-types

open import order-theory.decidable-total-orders
```

</details>

## Idea

The
{{#concept "minimum" Disambiguation="of positive rational numbers" Agda=min-ℚ⁺}}
of two
[positive rational numbers](elementary-number-theory.positive-rational-numbers.md)
is the
[smallest](elementary-number-theory.inequality-positive-rational-numbers.md) of
the two.

## Definition

```agda
abstract
  is-positive-min-ℚ :
    {p q : ℚ} → is-positive-ℚ p → is-positive-ℚ q → is-positive-ℚ (min-ℚ p q)
  is-positive-min-ℚ {p} {q} is-pos-p is-pos-q =
    is-positive-le-zero-ℚ _
      ( le-min-le-both-ℚ zero-ℚ p q
        ( le-zero-is-positive-ℚ p is-pos-p)
        ( le-zero-is-positive-ℚ q is-pos-q))

min-ℚ⁺ : ℚ⁺ → ℚ⁺ → ℚ⁺
min-ℚ⁺ (p , is-pos-p) (q , is-pos-q) =
  ( min-ℚ p q , is-positive-min-ℚ is-pos-p is-pos-q)
```

## Properties

### The binary minimum is associative

```agda
abstract
  associative-min-ℚ⁺ :
    (x y z : ℚ⁺) → min-ℚ⁺ (min-ℚ⁺ x y) z ＝ min-ℚ⁺ x (min-ℚ⁺ y z)
  associative-min-ℚ⁺ (x , _) (y , _) (z , _) = eq-ℚ⁺ (associative-min-ℚ x y z)
```

### The binary minimum is commutative

```agda
abstract
  commutative-min-ℚ⁺ : (x y : ℚ⁺) → min-ℚ⁺ x y ＝ min-ℚ⁺ y x
  commutative-min-ℚ⁺ (x , _) (y , _) = eq-ℚ⁺ (commutative-min-ℚ x y)
```

### The binary minimum is idempotent

```agda
abstract
  idempotent-min-ℚ⁺ : (x : ℚ⁺) → min-ℚ⁺ x x ＝ x
  idempotent-min-ℚ⁺ (x , _) = eq-ℚ⁺ (idempotent-min-ℚ x)
```

### The binary minimum is a lower bound

```agda
abstract
  leq-left-min-ℚ⁺ : (x y : ℚ⁺) → leq-ℚ⁺ (min-ℚ⁺ x y) x
  leq-left-min-ℚ⁺ (x , _) (y , _) = leq-left-min-ℚ x y

  leq-right-min-ℚ⁺ : (x y : ℚ⁺) → leq-ℚ⁺ (min-ℚ⁺ x y) y
  leq-right-min-ℚ⁺ (x , _) (y , _) = leq-right-min-ℚ x y
```

### Any two positive rational numbers have a positive rational number strictly less than both

```agda
module _
  (x y : ℚ⁺)
  where

  mediant-zero-min-ℚ⁺ : ℚ⁺
  mediant-zero-min-ℚ⁺ = mediant-zero-ℚ⁺ (min-ℚ⁺ x y)

  abstract
    le-left-mediant-zero-min-ℚ⁺ : le-ℚ⁺ mediant-zero-min-ℚ⁺ x
    le-left-mediant-zero-min-ℚ⁺ =
      concatenate-le-leq-ℚ
        ( rational-ℚ⁺ mediant-zero-min-ℚ⁺)
        ( rational-ℚ⁺ (min-ℚ⁺ x y))
        ( rational-ℚ⁺ x)
        ( le-mediant-zero-ℚ⁺ (min-ℚ⁺ x y))
        ( leq-left-min-ℚ⁺ x y)

    le-right-mediant-zero-min-ℚ⁺ : le-ℚ⁺ mediant-zero-min-ℚ⁺ y
    le-right-mediant-zero-min-ℚ⁺ =
      concatenate-le-leq-ℚ
        ( rational-ℚ⁺ mediant-zero-min-ℚ⁺)
        ( rational-ℚ⁺ (min-ℚ⁺ x y))
        ( rational-ℚ⁺ y)
        ( le-mediant-zero-ℚ⁺ (min-ℚ⁺ x y))
        ( leq-right-min-ℚ⁺ x y)
```
