# Exponentiation of natural numbers

```agda
module elementary-number-theory.exponentiation-natural-numbers where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.powers-of-elements-commutative-semirings

open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.bounded-divisibility-natural-numbers
open import elementary-number-theory.commutative-semiring-of-natural-numbers
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.multiplication-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.products-of-natural-numbers
open import elementary-number-theory.strict-inequality-natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.unit-type
```

</details>

## Idea

The {{#concept "exponential" Agda=exp-ℕ WD="exponentiation" WDID=Q33456}} $m^n$
of two [natural numbers](elementary-number-theory.natural-numbers.md) is the
number obtained by multiplying $m$ with itself $n$ times.

The natural numbers satisfy Tarski's high school arithmetic laws for exponentiation.

## Definition

### Exponentiation of natural numbers

```agda
power-ℕ : ℕ → ℕ → ℕ
power-ℕ = power-Commutative-Semiring ℕ-Commutative-Semiring

exp-ℕ : ℕ → ℕ → ℕ
exp-ℕ m n = power-ℕ n m

infixr 45 _^ℕ_
_^ℕ_ = exp-ℕ
```

## Properties

### `1ⁿ ＝ 1`

```agda
annihilation-law-exp-ℕ : (n : ℕ) → 1 ^ℕ n ＝ 1
annihilation-law-exp-ℕ = power-one-Commutative-Semiring ℕ-Commutative-Semiring
```

### `xⁿ⁺¹ = xⁿx`

```agda
exp-succ-ℕ :
  (n : ℕ) (x : ℕ) → x ^ℕ succ-ℕ n ＝ x ^ℕ n *ℕ x
exp-succ-ℕ =
  power-succ-Commutative-Semiring ℕ-Commutative-Semiring
```

### `xⁿ⁺¹ ＝ xxⁿ`

```agda
exp-succ-ℕ' :
  (n : ℕ) (x : ℕ) → x ^ℕ succ-ℕ n ＝ x *ℕ x ^ℕ n
exp-succ-ℕ' =
  power-succ-Commutative-Semiring' ℕ-Commutative-Semiring
```

### Powers by sums of natural numbers are products of powers

```agda
left-distributive-exp-add-ℕ :
  (m n : ℕ) {x : ℕ} → x ^ℕ (m +ℕ n) ＝ x ^ℕ m *ℕ x ^ℕ n
left-distributive-exp-add-ℕ =
  distributive-power-add-Commutative-Semiring ℕ-Commutative-Semiring
```

### Powers distribute over products

```agda
right-distributive-exp-mul-ℕ :
  (n : ℕ) (x y : ℕ) → (x *ℕ y) ^ℕ n ＝ x ^ℕ n *ℕ y ^ℕ n
right-distributive-exp-mul-ℕ =
  distributive-power-mul-Commutative-Semiring ℕ-Commutative-Semiring
```

### Powers by products of natural numbers are iterated powers

```agda
exp-mul-ℕ :
  (m n : ℕ) {x : ℕ} → x ^ℕ (m *ℕ n) ＝ (x ^ℕ m) ^ℕ n
exp-mul-ℕ =
  power-mul-Commutative-Semiring ℕ-Commutative-Semiring
```

### The exponent $m^n$ is nonzero if $m$ is nonzero

```agda
is-nonzero-exp-ℕ :
  (m n : ℕ) → is-nonzero-ℕ m → is-nonzero-ℕ (m ^ℕ n)
is-nonzero-exp-ℕ m zero-ℕ H =
  is-nonzero-one-ℕ
is-nonzero-exp-ℕ m (succ-ℕ zero-ℕ) H = H
is-nonzero-exp-ℕ m (succ-ℕ (succ-ℕ n)) H =
  is-nonzero-mul-ℕ (m ^ℕ succ-ℕ n) m (is-nonzero-exp-ℕ m (succ-ℕ n) H) H

le-zero-exp-ℕ :
  (m n : ℕ) → 0 <-ℕ m → 0 <-ℕ m ^ℕ n
le-zero-exp-ℕ m zero-ℕ H =
  star
le-zero-exp-ℕ m (succ-ℕ zero-ℕ) H =
  H
le-zero-exp-ℕ m (succ-ℕ (succ-ℕ n)) H =
  preserves-strict-order-mul-ℕ
    ( 0)
    ( m ^ℕ succ-ℕ n)
    ( 0)
    ( m)
    ( le-zero-exp-ℕ m (succ-ℕ n) H)
    ( H)

leq-one-exp-ℕ :
  (m n : ℕ) → 1 ≤-ℕ m → 1 ≤-ℕ m ^ℕ n
leq-one-exp-ℕ m n H =
  leq-one-is-nonzero-ℕ
    ( m ^ℕ n)
    ( is-nonzero-exp-ℕ m n (is-nonzero-leq-one-ℕ m H))
```

### The exponent $m^n$ is equal to the $n$-fold product of $m$

```agda
compute-constant-product-ℕ :
  (m n : ℕ) → Π-ℕ n (λ _ → m) ＝ exp-ℕ m n
compute-constant-product-ℕ m zero-ℕ = refl
compute-constant-product-ℕ m (succ-ℕ zero-ℕ) = left-unit-law-add-ℕ m
compute-constant-product-ℕ m (succ-ℕ (succ-ℕ n)) =
  ap (_*ℕ m) (compute-constant-product-ℕ m (succ-ℕ n))
```

### The base of the exponent divides its successor exponents

```text
bounded-div-exp-succ-ℕ :
  (m n : ℕ) → bounded-div-ℕ m (m ^ℕ succ-ℕ n)
pr1 (bounded-div-exp-succ-ℕ m n) = m ^ℕ n
pr1 (pr2 (bounded-div-exp-succ-ℕ m n)) = {!!}
pr2 (pr2 (bounded-div-exp-succ-ℕ m n)) = {!!}
```
