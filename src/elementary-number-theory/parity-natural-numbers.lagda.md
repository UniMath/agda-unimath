# Parity of the natural numbers

```agda
module elementary-number-theory.parity-natural-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.divisibility-natural-numbers
open import elementary-number-theory.equality-natural-numbers
open import elementary-number-theory.modular-arithmetic-standard-finite-types
open import elementary-number-theory.multiplication-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.function-types
open import foundation.identity-types
open import foundation.negated-equality
open import foundation.negation
open import foundation.transport-along-identifications
open import foundation.universe-levels
```

</details>

## Idea

Parity partitions the natural numbers into two classes: the even and the odd
natural numbers. Even natural numbers are those that are divisible by two, and
odd natural numbers are those that aren't.

## Definition

```agda
is-even-ℕ : ℕ → UU lzero
is-even-ℕ n = div-ℕ 2 n

is-odd-ℕ : ℕ → UU lzero
is-odd-ℕ n = ¬ (is-even-ℕ n)
```

## Properties

### Being even or odd is decidable

```agda
is-decidable-is-even-ℕ : (x : ℕ) → is-decidable (is-even-ℕ x)
is-decidable-is-even-ℕ x = is-decidable-div-ℕ 2 x

is-decidable-is-odd-ℕ : (x : ℕ) → is-decidable (is-odd-ℕ x)
is-decidable-is-odd-ℕ x = is-decidable-neg (is-decidable-is-even-ℕ x)
```

### `0` is an even natural number

```agda
is-even-zero-ℕ : is-even-ℕ 0
is-even-zero-ℕ = div-zero-ℕ 2

is-odd-one-ℕ : is-odd-ℕ 1
is-odd-one-ℕ H = Eq-eq-ℕ (is-one-div-one-ℕ 2 H)
```

### A natural number `x` is even if and only if `x + 2` is even

```agda
abstract
  is-even-is-even-succ-succ-ℕ :
    (n : ℕ) → is-even-ℕ (succ-ℕ (succ-ℕ n)) → is-even-ℕ n
  pr1 (is-even-is-even-succ-succ-ℕ n (succ-ℕ d , p)) = d
  pr2 (is-even-is-even-succ-succ-ℕ n (succ-ℕ d , p)) =
    is-injective-succ-ℕ (is-injective-succ-ℕ p)

  is-even-succ-succ-is-even-ℕ :
    (n : ℕ) → is-even-ℕ n → is-even-ℕ (succ-ℕ (succ-ℕ n))
  pr1 (is-even-succ-succ-is-even-ℕ n (d , p)) = succ-ℕ d
  pr2 (is-even-succ-succ-is-even-ℕ n (d , p)) = ap (succ-ℕ ∘ succ-ℕ) p
```

### A natural number `x` is odd if and only if `x + 2` is odd

```agda
abstract
  is-odd-is-odd-succ-succ-ℕ :
    (n : ℕ) → is-odd-ℕ (succ-ℕ (succ-ℕ n)) → is-odd-ℕ n
  is-odd-is-odd-succ-succ-ℕ n = map-neg (is-even-succ-succ-is-even-ℕ n)

  is-odd-succ-succ-is-odd-ℕ :
    (n : ℕ) → is-odd-ℕ n → is-odd-ℕ (succ-ℕ (succ-ℕ n))
  is-odd-succ-succ-is-odd-ℕ n = map-neg (is-even-is-even-succ-succ-ℕ n)
```

### If a natural number `x` is odd, then `x + 1` is even

```agda
abstract
  is-even-succ-is-odd-ℕ :
    (n : ℕ) → is-odd-ℕ n → is-even-ℕ (succ-ℕ n)
  is-even-succ-is-odd-ℕ zero-ℕ p = ex-falso (p is-even-zero-ℕ)
  is-even-succ-is-odd-ℕ (succ-ℕ zero-ℕ) p = (1 , refl)
  is-even-succ-is-odd-ℕ (succ-ℕ (succ-ℕ n)) p =
    is-even-succ-succ-is-even-ℕ
      ( succ-ℕ n)
      ( is-even-succ-is-odd-ℕ n (is-odd-is-odd-succ-succ-ℕ n p))
```

### If a natural number `x` is even, then `x + 1` is odd

```agda
abstract
  is-odd-succ-is-even-ℕ :
    (n : ℕ) → is-even-ℕ n → is-odd-ℕ (succ-ℕ n)
  is-odd-succ-is-even-ℕ zero-ℕ p = is-odd-one-ℕ
  is-odd-succ-is-even-ℕ (succ-ℕ zero-ℕ) p = ex-falso (is-odd-one-ℕ p)
  is-odd-succ-is-even-ℕ (succ-ℕ (succ-ℕ n)) p =
    is-odd-succ-succ-is-odd-ℕ
      ( succ-ℕ n)
      ( is-odd-succ-is-even-ℕ n (is-even-is-even-succ-succ-ℕ n p))
```

### If a natural number `x + 1` is odd, then `x` is even

```agda
abstract
  is-even-is-odd-succ-ℕ :
    (n : ℕ) → is-odd-ℕ (succ-ℕ n) → is-even-ℕ n
  is-even-is-odd-succ-ℕ n p =
    is-even-is-even-succ-succ-ℕ
      ( n)
      ( is-even-succ-is-odd-ℕ (succ-ℕ n) p)
```

### If a natural number `x + 1` is even, then `x` is odd

```agda
abstract
  is-odd-is-even-succ-ℕ :
    (n : ℕ) → is-even-ℕ (succ-ℕ n) → is-odd-ℕ n
  is-odd-is-even-succ-ℕ n p =
    is-odd-is-odd-succ-succ-ℕ
      ( n)
      ( is-odd-succ-is-even-ℕ (succ-ℕ n) p)
```

### A natural number `x` is odd if and only if there is a natural number `y` such that `succ-ℕ (y *ℕ 2) ＝ x`

```agda
has-odd-expansion : ℕ → UU lzero
has-odd-expansion x = Σ ℕ (λ y → (succ-ℕ (y *ℕ 2)) ＝ x)

abstract
  is-odd-has-odd-expansion : (n : ℕ) → has-odd-expansion n → is-odd-ℕ n
  is-odd-has-odd-expansion .(succ-ℕ (m *ℕ 2)) (m , refl) =
    is-odd-succ-is-even-ℕ (m *ℕ 2) (m , refl)

  has-odd-expansion-is-odd : (n : ℕ) → is-odd-ℕ n → has-odd-expansion n
  has-odd-expansion-is-odd zero-ℕ p = ex-falso (p is-even-zero-ℕ)
  has-odd-expansion-is-odd (succ-ℕ zero-ℕ) p = 0 , refl
  has-odd-expansion-is-odd (succ-ℕ (succ-ℕ n)) p =
    ( succ-ℕ (pr1 s)) , ap (succ-ℕ ∘ succ-ℕ) (pr2 s)
    where
    s : has-odd-expansion n
    s = has-odd-expansion-is-odd n (is-odd-is-odd-succ-succ-ℕ n p)
```

### If `x` is odd and `y` is even, `x ≠ y`

```agda
abstract
  noneq-odd-even :
    (x y : ℕ) → is-odd-ℕ x → is-even-ℕ y → x ≠ y
  noneq-odd-even x y odd-x even-y x=y = odd-x (inv-tr is-even-ℕ x=y even-y)
```
