# Fermat numbers

```agda
module elementary-number-theory.fermat-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.exponentiation-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.products-of-natural-numbers
open import elementary-number-theory.strong-induction-natural-numbers

open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

{{#concept "Fermat numbers"}} are numbers of the form $F_n := 2^{2^n}+1$. The
first five Fermat numbers are

```text
  3, 5, 17, 257, and 65537.
```

The sequence of Fermat numbers is listed as A000215 in the
[Online Encyclopedia of Integer Sequences](online-encyclopedia-of-integer-sequences.oeis.md).

Alternatively, the Fermat numbers can be defined with
[strong induction](elementary-number-theory.strong-induction-natural-numbers.md)
by

```text
F 0 := 3
F (n + 1) := 2 + Π_{i≤n} F_i
```

This recurrence implies that any two Fermat numbers are
[relatively prime](elementary-number-theory.relatively-prime-natural-numbers.md).
Goldbach used this observation to prove the
[infinitude of primes](elementary-number-theory.infinitude-of-primes.md): Since
there are infinitely many Fermat numbers, and all of them are relatively prime,
there must be infinitely many prime numbers. Fermat numbers also feature in a
series of long-standing open problems in mathematics, including:

- Are there infinitely many prime Fermat numbers?
- Is $F_n$ composite for all $n\geq 5$?

## Definition

### The Fermat numbers

```agda
fermat-number-ℕ : ℕ → ℕ
fermat-number-ℕ n = exp-ℕ 2 (exp-ℕ 2 n) +ℕ 1
```

### The recursive definition of the Fermat numbers

```agda
recursive-fermat-number-ℕ : ℕ → ℕ
recursive-fermat-number-ℕ =
  strong-rec-ℕ 3
    ( λ n f →
      add-ℕ
        ( Π-ℕ
          ( succ-ℕ n)
          ( λ i → f (nat-Fin (succ-ℕ n) i) (upper-bound-nat-Fin n i)))
        ( 2))
```
