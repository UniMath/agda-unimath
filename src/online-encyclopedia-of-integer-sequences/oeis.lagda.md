# Sequences of the online encyclopedia of integer sequences

```agda
module online-encyclopedia-of-integer-sequences.oeis where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.eulers-totient-function
open import elementary-number-theory.exponentiation-natural-numbers
open import elementary-number-theory.factorials
open import elementary-number-theory.fibonacci-sequence
open import elementary-number-theory.natural-numbers

open import finite-group-theory.finite-groups

open import foundation.functions
```

</details>

```agda
A000001 : ℕ → ℕ
A000001 = number-of-groups-of-order

A000010 : ℕ → ℕ
A000010 = eulers-totient-function

A000045 : ℕ → ℕ
A000045 = Fibonacci-ℕ

A000079 : ℕ → ℕ
A000079 = exp-ℕ 2

A000142 : ℕ → ℕ
A000142 = factorial-ℕ

A000244 : ℕ → ℕ
A000244 = exp-ℕ 3

A001477 : ℕ → ℕ
A001477 = id
```
