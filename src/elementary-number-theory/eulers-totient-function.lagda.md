# Euler's totient function

```agda
module elementary-number-theory.eulers-totient-function where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.relatively-prime-natural-numbers

open import univalent-combinatorics.decidable-subtypes
open import univalent-combinatorics.finite-types
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

{{#concept "Euler's totient function" WD="Euler's totient function" WDID=Q190026 Agda=eulers-totient-function-relatively-prime}}
`φ : ℕ → ℕ` is the function that maps a
[natural number](elementary-number-theory.natural-numbers.md) `n` to the number
of
[multiplicative units modulo `n`](elementary-number-theory.multiplicative-units-standard-cyclic-rings.md).
In other words, the number `φ n` is the cardinality of the
[group of units](ring-theory.groups-of-units-rings.md) of the
[ring](ring-theory.rings.md) `ℤ-Mod n`.

Alternatively, Euler's totient function can be defined as the function `ℕ → ℕ`
that returns for each `n` the number of `x < n` that are
[relatively prime](elementary-number-theory.relatively-prime-natural-numbers.md).
These two definitions of Euler's totient function agree on the _positive_
natural numbers. However, there are two multiplicative units in the
[ring `ℤ`](elementary-number-theory.ring-of-integers.md) of
[integers](elementary-number-theory.integers.md), while there are no natural
numbers `x < 0` that are relatively prime to `0`.

Our reason for preferring the first definition over the second definition is
that the usual properties of Euler's totient function, such as multiplicativity,
extend naturally to the first definition.

## Definitions

### The definition of Euler's totient function using relatively prime natural numbers

```agda
eulers-totient-function-relatively-prime : ℕ → ℕ
eulers-totient-function-relatively-prime n =
  number-of-elements-subset-Finite-Type
    ( Fin-Finite-Type n)
    ( λ x → is-relatively-prime-ℕ-Decidable-Prop (nat-Fin n x) n)
```

## See also

### Table of files related to cyclic types, groups, and rings

{{#include tables/cyclic-types.md}}

## External links

- [Euler's totient function](https://en.wikipedia.org/wiki/Euler%27s_totient_function)
  at Wikipedia
- [Totient Function](https://mathworld.wolfram.com/TotientFunction.html) at
  Wolfram MathWorld
