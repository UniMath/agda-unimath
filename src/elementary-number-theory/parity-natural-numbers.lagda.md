# Parity of the natural numbers

```agda
module elementary-number-theory.parity-natural-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.divisibility-natural-numbers
open import elementary-number-theory.modular-arithmetic-standard-finite-types
open import elementary-number-theory.natural-numbers

open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.functions
open import foundation.identity-types
open import foundation.negation
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
is-odd-is-odd-succ-succ-ℕ :
  (n : ℕ) → is-odd-ℕ (succ-ℕ (succ-ℕ n)) → is-odd-ℕ n
is-odd-is-odd-succ-succ-ℕ n = map-neg (is-even-succ-succ-is-even-ℕ n)

is-odd-succ-succ-is-odd-ℕ :
  (n : ℕ) → is-odd-ℕ n → is-odd-ℕ (succ-ℕ (succ-ℕ n))
is-odd-succ-succ-is-odd-ℕ n = map-neg (is-even-is-even-succ-succ-ℕ n)
```
