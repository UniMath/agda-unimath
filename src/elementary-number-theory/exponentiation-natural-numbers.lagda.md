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
open import elementary-number-theory.divisibility-natural-numbers
open import elementary-number-theory.equality-natural-numbers
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.multiplication-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.products-of-natural-numbers
open import elementary-number-theory.strict-inequality-natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.empty-types
open import foundation.identity-types
open import foundation.injective-maps
open import foundation.unit-type

open import order-theory.order-preserving-maps-posets
open import order-theory.strict-order-preserving-maps
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

### `mⁿ⁺¹ = mⁿm`

```agda
exp-succ-ℕ :
  (m n : ℕ) → m ^ℕ succ-ℕ n ＝ m ^ℕ n *ℕ m
exp-succ-ℕ m n =
  power-succ-Commutative-Semiring ℕ-Commutative-Semiring n m
```

### `mⁿ⁺¹ ＝ mmⁿ`

```agda
exp-succ-ℕ' :
  (m n : ℕ) → m ^ℕ succ-ℕ n ＝ m *ℕ m ^ℕ n
exp-succ-ℕ' m n =
  power-succ-Commutative-Semiring' ℕ-Commutative-Semiring n m
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

### The exponent $m^n$ of a number $m>1$ by a nonzero number $n$ is strictly greater than $0$

```agda
le-one-exp-ℕ :
  (m n : ℕ) → 1 <-ℕ m → is-nonzero-ℕ n → 1 <-ℕ m ^ℕ n
le-one-exp-ℕ (succ-ℕ (succ-ℕ m)) zero-ℕ H K = ex-falso (K refl)
le-one-exp-ℕ (succ-ℕ (succ-ℕ m)) (succ-ℕ zero-ℕ) H K = star
le-one-exp-ℕ (succ-ℕ (succ-ℕ m)) (succ-ℕ (succ-ℕ n)) H K =
  concatenate-le-leq-ℕ 1
    ( succ-ℕ (succ-ℕ m) ^ℕ succ-ℕ n)
    ( succ-ℕ (succ-ℕ m) ^ℕ succ-ℕ (succ-ℕ n))
    ( le-one-exp-ℕ (succ-ℕ (succ-ℕ m)) (succ-ℕ n) H (is-nonzero-succ-ℕ n))
    ( concatenate-eq-leq-eq-ℕ
      ( inv (right-unit-law-mul-ℕ (succ-ℕ (succ-ℕ m) ^ℕ succ-ℕ n)))
      ( preserves-order-right-mul-ℕ
        ( succ-ℕ (succ-ℕ m) ^ℕ succ-ℕ n)
        ( 1)
        ( succ-ℕ (succ-ℕ m))
        ( star))
      ( exp-succ-ℕ (succ-ℕ (succ-ℕ m)) (succ-ℕ n)))
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

```agda
div-exp-succ-ℕ :
  (m n : ℕ) → div-ℕ m (m ^ℕ succ-ℕ n)
pr1 (div-exp-succ-ℕ m n) = m ^ℕ n
pr2 (div-exp-succ-ℕ m n) = inv (exp-succ-ℕ m n)

div-exp-is-successor-ℕ :
  (m n : ℕ) → is-successor-ℕ n → div-ℕ m (m ^ℕ n)
div-exp-is-successor-ℕ m .(succ-ℕ k) (k , refl) =
  div-exp-succ-ℕ m k

div-exp-ℕ :
  (m n : ℕ) → is-nonzero-ℕ n → div-ℕ m (m ^ℕ n)
div-exp-ℕ m n H =
  div-exp-is-successor-ℕ m n (is-successor-is-nonzero-ℕ H)

bounded-div-exp-ℕ :
  (m n : ℕ) → is-nonzero-ℕ n → bounded-div-ℕ m (m ^ℕ n)
bounded-div-exp-ℕ m n H =
  bounded-div-div-ℕ m (m ^ℕ n) (div-exp-ℕ m n H)
```

### If an exponential of a number greater than $1$ is equal to $1$, then its exponent is $0$

```agda
is-zero-exponent-is-one-exp-ℕ :
  (m n : ℕ) → 1 <-ℕ m → is-one-ℕ (m ^ℕ n) → is-zero-ℕ n
is-zero-exponent-is-one-exp-ℕ m zero-ℕ H K =
  refl
is-zero-exponent-is-one-exp-ℕ m (succ-ℕ n) H p =
  ex-falso
    ( neq-le-ℕ
      ( concatenate-leq-le-ℕ 1
        ( m ^ℕ n)
        ( m ^ℕ n *ℕ m)
        ( leq-one-exp-ℕ m n (leq-le-ℕ 1 m H))
        ( concatenate-eq-le-ℕ
          ( m ^ℕ n)
          ( m ^ℕ n *ℕ 1)
          ( m ^ℕ n *ℕ m)
          ( inv (right-unit-law-mul-ℕ (m ^ℕ n)))
          ( preserves-strict-order-left-mul-ℕ
            ( m ^ℕ n)
            ( 1)
            ( m)
            ( is-nonzero-exp-ℕ m n (is-nonzero-le-ℕ 1 m H)) H)))
      ( inv p ∙ exp-succ-ℕ m n))
```

### The function $n \mapsto m^n$ is injective and an embedding for any $m>1$

```agda
is-injective-exp-ℕ :
  (m : ℕ) → 1 <-ℕ m → is-injective (m ^ℕ_)
is-injective-exp-ℕ m H {zero-ℕ} {zero-ℕ} p =
  refl
is-injective-exp-ℕ m H {zero-ℕ} {succ-ℕ l} p =
  inv (is-zero-exponent-is-one-exp-ℕ m (succ-ℕ l) H (inv p))
is-injective-exp-ℕ m H {succ-ℕ k} {zero-ℕ} p =
  is-zero-exponent-is-one-exp-ℕ m (succ-ℕ k) H p
is-injective-exp-ℕ m H {succ-ℕ k} {succ-ℕ l} p =
  ap
    ( succ-ℕ)
    ( is-injective-exp-ℕ m H {k} {l}
      ( is-injective-right-mul-ℕ m
        ( is-nonzero-le-ℕ 1 m H)
        ( inv (exp-succ-ℕ m k) ∙ p ∙ exp-succ-ℕ m l)))

is-emb-exp-ℕ :
  (m : ℕ) → 1 <-ℕ m → is-emb (m ^ℕ_)
is-emb-exp-ℕ m H =
  is-emb-is-injective is-set-ℕ (is-injective-exp-ℕ m H)
```

### Exponentiating a nonzero number is an order preserving function

```agda
preserves-order-exponent-exp-ℕ :
  (m : ℕ) → is-nonzero-ℕ m →
  preserves-order-Poset ℕ-Poset ℕ-Poset (m ^ℕ_)
preserves-order-exponent-exp-ℕ m H zero-ℕ zero-ℕ K =
  refl-leq-ℕ 1
preserves-order-exponent-exp-ℕ m H zero-ℕ (succ-ℕ k) K =
  leq-one-exp-ℕ m (succ-ℕ k) (leq-one-is-nonzero-ℕ m H)
preserves-order-exponent-exp-ℕ m H (succ-ℕ n) (succ-ℕ k) K =
  concatenate-eq-leq-eq-ℕ
    ( exp-succ-ℕ m n)
    ( preserves-order-mul-ℕ
      ( m ^ℕ n)
      ( m ^ℕ k)
      ( m)
      ( m)
      ( preserves-order-exponent-exp-ℕ m H n k K)
      ( refl-leq-ℕ m))
    ( inv (exp-succ-ℕ m k))
```

### Exponentiating a number strictly greater than $1$ is a strictly order preserving function

```agda
preserves-strict-order-exponent-exp-ℕ :
  (m : ℕ) → 1 <-ℕ m →
  preserves-strict-order-map-Strictly-Ordered-Type
    ( ℕ-Strictly-Ordered-Type)
    ( ℕ-Strictly-Ordered-Type)
    ( m ^ℕ_)
preserves-strict-order-exponent-exp-ℕ m H zero-ℕ (succ-ℕ k) K =
  le-one-exp-ℕ m (succ-ℕ k) H (is-nonzero-succ-ℕ k)
preserves-strict-order-exponent-exp-ℕ m H (succ-ℕ n) (succ-ℕ k) K =
  concatenate-eq-le-eq-ℕ
    ( m ^ℕ succ-ℕ n)
    ( m ^ℕ n *ℕ m)
    ( m ^ℕ k *ℕ m)
    ( m ^ℕ succ-ℕ k)
    ( exp-succ-ℕ m n)
    ( preserves-strict-order-right-mul-ℕ
      ( m)
      ( m ^ℕ n)
      ( m ^ℕ k)
      ( is-nonzero-le-ℕ 1 m H)
      ( preserves-strict-order-exponent-exp-ℕ m H n k K))
    ( inv (exp-succ-ℕ m k))
```
