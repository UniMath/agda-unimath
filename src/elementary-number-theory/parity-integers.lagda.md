# Parity of the integers

```agda
module elementary-number-theory.parity-integers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.absolute-value-integers
open import elementary-number-theory.addition-integers
open import elementary-number-theory.divisibility-integers
open import elementary-number-theory.integers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.parity-natural-numbers

open import foundation.decidable-types
open import foundation.negation
open import foundation.universe-levels
```

</details>

## Idea

{{#concept "Parity" WD="parity" WDID=Q141160}}
[partitions](foundation.partitions.md) the
[integers](elementary-number-theory.integers.md) into two
[classes](foundation.equivalence-relations.md): the
{{#concept "even" Disambiguation="integer" Agda=is-even-ℤ WD="even number" WDID=Q13366104}}
and the
{{#concept "odd" Disambiguation="integer" Agda=is-odd-ℤ WD="odd number" WDID=Q13366129}}
integers. Even integers are those that are
[divisible](elementary-number-theory.divisibility-integers.md) by two, and odd
integers are those that aren't.

## Definitions

### Even and odd integers

```agda
is-even-ℤ : ℤ → UU lzero
is-even-ℤ a = div-ℤ (int-ℕ 2) a

is-odd-ℤ : ℤ → UU lzero
is-odd-ℤ a = ¬ (is-even-ℤ a)
```

## Properties

### A natural number is even if and only if it is even as an integer

```agda
is-even-int-is-even-ℕ : (n : ℕ) → is-even-ℕ n → is-even-ℤ (int-ℕ n)
is-even-int-is-even-ℕ n H = div-int-div-ℕ H

is-even-is-even-int-ℕ : (n : ℕ) → is-even-ℤ (int-ℕ n) → is-even-ℕ n
is-even-is-even-int-ℕ n H = div-div-int-ℕ H
```

### A natural number is odd if and only if it is odd as an integer

```agda
is-odd-int-is-odd-ℕ : (n : ℕ) → is-odd-ℕ n → is-odd-ℤ (int-ℕ n)
is-odd-int-is-odd-ℕ n H K = H (is-even-is-even-int-ℕ n K)

is-odd-is-odd-int-ℕ : (n : ℕ) → is-odd-ℤ (int-ℕ n) → is-odd-ℕ n
is-odd-is-odd-int-ℕ n H K = H (is-even-int-is-even-ℕ n K)
```

### An integer is even if and only if its absolute value is an even integer

```agda
is-even-int-abs-is-even-ℤ :
  (a : ℤ) → is-even-ℤ a → is-even-ℤ (int-abs-ℤ a)
is-even-int-abs-is-even-ℤ a =
  div-sim-unit-ℤ
    ( refl-sim-unit-ℤ (int-ℕ 2))
    ( symmetric-sim-unit-ℤ (int-abs-ℤ a) a (sim-unit-abs-ℤ a))

is-even-is-even-int-abs-ℤ :
  (a : ℤ) → is-even-ℤ (int-abs-ℤ a) → is-even-ℤ a
is-even-is-even-int-abs-ℤ a =
  div-sim-unit-ℤ
    ( refl-sim-unit-ℤ (int-ℕ 2))
    ( sim-unit-abs-ℤ a)

is-even-abs-is-even-ℤ :
  (a : ℤ) → is-even-ℤ a → is-even-ℕ (abs-ℤ a)
is-even-abs-is-even-ℤ a H =
  is-even-is-even-int-ℕ (abs-ℤ a) (is-even-int-abs-is-even-ℤ a H)

is-even-is-even-abs-ℤ :
  (a : ℤ) → is-even-ℕ (abs-ℤ a) → is-even-ℤ a
is-even-is-even-abs-ℤ a H =
  is-even-is-even-int-abs-ℤ a (is-even-int-is-even-ℕ (abs-ℤ a) H)
```

### An integer is odd if and only if its absolute value is an odd integer

```agda
is-odd-int-abs-is-odd-ℤ : (a : ℤ) → is-odd-ℤ a → is-odd-ℤ (int-abs-ℤ a)
is-odd-int-abs-is-odd-ℤ a H K = H (is-even-is-even-int-abs-ℤ a K)

is-odd-is-odd-int-abs-ℤ : (a : ℤ) → is-odd-ℤ (int-abs-ℤ a) → is-odd-ℤ a
is-odd-is-odd-int-abs-ℤ a H K = H (is-even-int-abs-is-even-ℤ a K)

is-odd-abs-is-odd-ℤ : (a : ℤ) → is-odd-ℤ a → is-odd-ℕ (abs-ℤ a)
is-odd-abs-is-odd-ℤ a H K = H (is-even-is-even-abs-ℤ a K)

is-odd-is-odd-abs-ℤ : (a : ℤ) → is-odd-ℕ (abs-ℤ a) → is-odd-ℤ a
is-odd-is-odd-abs-ℤ a H K = H (is-even-abs-is-even-ℤ a K)
```

### Being even or odd is decidable

```agda
is-decidable-is-even-ℤ :
  (a : ℤ) → is-decidable (is-even-ℤ a)
is-decidable-is-even-ℤ a =
  is-decidable-iff
    ( is-even-is-even-abs-ℤ a)
    ( is-even-abs-is-even-ℤ a)
    ( is-decidable-is-even-ℕ (abs-ℤ a))

is-decidable-is-odd-ℤ : (a : ℤ) → is-decidable (is-odd-ℤ a)
is-decidable-is-odd-ℤ a = is-decidable-neg (is-decidable-is-even-ℤ a)
```

### `0` is an even integer

```agda
is-even-zero-ℤ : is-even-ℤ (int-ℕ 0)
is-even-zero-ℤ = is-even-int-is-even-ℕ 0 is-even-zero-ℕ
```

### `1` is an odd integer

```agda
is-odd-one-ℤ : is-odd-ℤ (int-ℕ 1)
is-odd-one-ℤ = is-odd-int-is-odd-ℕ 1 is-odd-one-ℕ
```

### A integer `x` is even if and only if `x + 2` is even

```agda
is-even-is-even-add-two-ℤ :
  (a : ℤ) → is-even-ℤ (a +ℤ int-ℕ 2) → is-even-ℤ a
is-even-is-even-add-two-ℤ a =
  div-left-summand-ℤ (int-ℕ 2) a (int-ℕ 2) (refl-div-ℤ (int-ℕ 2))

is-even-add-two-is-even-ℤ :
  (a : ℤ) → is-even-ℤ a → is-even-ℤ (a +ℤ int-ℕ 2)
is-even-add-two-is-even-ℤ a H =
  div-add-ℤ (int-ℕ 2) a (int-ℕ 2) H (refl-div-ℤ (int-ℕ 2))
```

### A integer `x` is odd if and only if `x + 2` is odd

```agda
is-odd-is-odd-add-two-ℤ : (a : ℤ) → is-odd-ℤ (a +ℤ int-ℕ 2) → is-odd-ℤ a
is-odd-is-odd-add-two-ℤ a H K = H (is-even-add-two-is-even-ℤ a K)

is-odd-add-two-is-odd-ℤ : (a : ℤ) → is-odd-ℤ a → is-odd-ℤ (a +ℤ int-ℕ 2)
is-odd-add-two-is-odd-ℤ a H K = H (is-even-is-even-add-two-ℤ a K)
```

### If a integer `x` is odd, then `x + 1` is even

```text
is-even-succ-is-odd-ℕ :
  (n : ℕ) → is-odd-ℕ n → is-even-ℕ (succ-ℕ n)
is-even-succ-is-odd-ℕ zero-ℕ p = ex-falso (p is-even-zero-ℕ)
is-even-succ-is-odd-ℕ (succ-ℕ zero-ℕ) p = (1 , refl)
is-even-succ-is-odd-ℕ (succ-ℕ (succ-ℕ n)) p =
  is-even-succ-succ-is-even-ℕ
    ( succ-ℕ n)
    ( is-even-succ-is-odd-ℕ n (is-odd-is-odd-succ-succ-ℕ n p))
```

### If a integer `x` is even, then `x + 1` is odd

```text
is-odd-succ-is-even-ℕ :
  (n : ℕ) → is-even-ℕ n → is-odd-ℕ (succ-ℕ n)
is-odd-succ-is-even-ℕ zero-ℕ p = is-odd-one-ℕ
is-odd-succ-is-even-ℕ (succ-ℕ zero-ℕ) p = ex-falso (is-odd-one-ℕ p)
is-odd-succ-is-even-ℕ (succ-ℕ (succ-ℕ n)) p =
  is-odd-succ-succ-is-odd-ℕ
    ( succ-ℕ n)
    ( is-odd-succ-is-even-ℕ n (is-even-is-even-succ-succ-ℕ n p))
```

### If a integer `x + 1` is odd, then `x` is even

```text
is-even-is-odd-succ-ℕ :
  (n : ℕ) → is-odd-ℕ (succ-ℕ n) → is-even-ℕ n
is-even-is-odd-succ-ℕ n p =
  is-even-is-even-succ-succ-ℕ
    ( n)
    ( is-even-succ-is-odd-ℕ (succ-ℕ n) p)
```

### If a integer `x + 1` is even, then `x` is odd

```text
is-odd-is-even-succ-ℕ :
  (n : ℕ) → is-even-ℕ (succ-ℕ n) → is-odd-ℕ n
is-odd-is-even-succ-ℕ n p =
  is-odd-is-odd-succ-succ-ℕ
    ( n)
    ( is-odd-succ-is-even-ℕ (succ-ℕ n) p)
```

### A integer `x` is odd if and only if there is a integer `y` such that `succ-ℕ (y *ℕ 2) ＝ x`

```text
has-odd-expansion : ℕ → UU lzero
has-odd-expansion x = Σ ℕ (λ y → (succ-ℕ (y *ℕ 2)) ＝ x)

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

### A number is even if and only if it is divisible by an even number

```text
is-even-div-is-even-ℕ :
  (n m : ℕ) → is-even-ℕ m → div-ℕ m n → is-even-ℕ n
is-even-div-is-even-ℕ ._ ._ (m' , refl) (k , refl) =
  k *ℕ m' , associative-mul-ℕ k m' 2

is-even-div-4-ℕ :
  (n : ℕ) → div-ℕ 4 n → is-even-ℕ n
is-even-div-4-ℕ n = is-even-div-is-even-ℕ n 4 (2 , refl)
```

### If any two out of `x`, `y`, and `x + y` are even, then so is the third

```text
is-even-add-ℕ :
  (m n : ℕ) → is-even-ℕ m → is-even-ℕ n → is-even-ℕ (add-ℕ m n)
is-even-add-ℕ = div-add-ℕ 2

is-even-left-summand-ℕ :
  (m n : ℕ) → is-even-ℕ n → is-even-ℕ (add-ℕ m n) → is-even-ℕ m
is-even-left-summand-ℕ = div-left-summand-ℕ 2

is-even-right-summand-ℕ :
  (m n : ℕ) → is-even-ℕ m → is-even-ℕ (add-ℕ m n) → is-even-ℕ n
is-even-right-summand-ℕ = div-right-summand-ℕ 2
```
