# Sequences of the online encyclopedia of integer sequences

This file records formalized sequences of the
[Online Encyclopedia of Integer Sequences](https://oeis.org) {{#cite oeis}}.

```agda
module literature.oeis where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.exponentiation-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.function-types
```

</details>

## Sequences

### The number of groups of order `n`

OEIS: [A000001](https://oeis.org/A000001)

```agda
open import finite-group-theory.finite-groups using
  ( number-of-groups-of-order)
```

### The Kolakoski sequence

OEIS: [A000002](https://oeis.org/A000002)

```agda
open import elementary-number-theory.kolakoski-sequence using
  ( kolakoski)
```

### The zero sequence

OEIS: [A000004](https://oeis.org/A000004)

```agda
A000004 : ℕ → ℕ
A000004 _ = zero-ℕ
```

### The characteristic function for 0

OEIS: [A000007](https://oeis.org/A000007)

```agda
A000007 : ℕ → ℕ
A000007 zero-ℕ = 1
A000007 (succ-ℕ _) = 0
```

### Euler's totient function

OEIS: [A000010](https://oeis.org/A000010)

```agda
open import elementary-number-theory.eulers-totient-function using
  ( eulers-totient-function-relatively-prime)
```

### All 1's sequence

OEIS: [A000012](https://oeis.org/A000012)

```agda
A000012 : ℕ → ℕ
A000012 _ = 1
```

### The positive integers

OEIS: [A000027](https://oeis.org/A000027)

```agda
A000027 : ℕ → ℕ
A000027 = succ-ℕ
```

### The prime numbers

OEIS: [A000040](https://oeis.org/A000040)

```agda
open import elementary-number-theory.infinitude-of-primes using
  ( prime-ℕ)
```

### The Fibonacci sequence

OEIS: [A000045](https://oeis.org/A000045)

```agda
open import elementary-number-theory.fibonacci-sequence using
  ( Fibonacci-ℕ)
```

### Sylvester's sequence

OEIS: [A000058](https://oeis.org/A000058)

```agda
open import elementary-number-theory.sylvesters-sequence using
  ( sylvesters-sequence-ℕ)
```

### Powers of `2`

OEIS: [A000079](https://oeis.org/A000079)

```agda
A000079 : ℕ → ℕ
A000079 = exp-ℕ 2
```

### The Catalan numbers

OEIS: [A000108](https://oeis.org/A000108)

```agda
open import elementary-number-theory.catalan-numbers using
  ( catalan-numbers)
```

### The Bell numbers

OEIS: [A000110](https://oeis.org/A000110)

```agda
open import elementary-number-theory.bell-numbers using
  ( bell-number-ℕ)
```

### Factorials

OEIS: [A000142](https://oeis.org/A000142)

```agda
open import elementary-number-theory.factorials using
  ( factorial-ℕ)
```

### The Fermat numbers

OEIS: [A000215](https://oeis.org/A000215)

```agda
open import elementary-number-theory.fermat-numbers using
  ( fermat-number-ℕ)
```

### Powers of `3`

OEIS: [A000244](https://oeis.org/A000244)

```agda
A000244 : ℕ → ℕ
A000244 = exp-ℕ 3
```

### The prime counting function

OEIS: [A000720](https://oeis.org/A000720)

```agda
open import elementary-number-theory.infinitude-of-primes using
  ( prime-counting-ℕ)
```

### The Euclid–Mullin sequence

OEIS: [A000945](https://oeis.org/A000945)

```agda
open import elementary-number-theory.euclid-mullin-sequence using
  ( euclid-mullin-ℕ)
```

### Pisano periods

OEIS: [A001175](https://oeis.org/A001175)

```agda
open import elementary-number-theory.pisano-periods using
  ( pisano-period)
```

### The cofibonacci sequence

OEIS: [A001177](https://oeis.org/A001177)

```agda
open import elementary-number-theory.cofibonacci using
  ( cofibonacci)
```

### The natural numbers

OEIS: [A001477](https://oeis.org/A001477)

```agda
A001477 : ℕ → ℕ
A001477 = id
```

### The number of main classes of Latin squares of order `n`

OEIS: [A003090](https://oeis.org/A003090)

```agda
open import univalent-combinatorics.main-classes-of-latin-squares using
  ( number-of-main-classes-of-Latin-squares-of-order)
```

### Collatz' bijection

OEIS: [A006369](https://oeis.org/A006369)

```agda
open import elementary-number-theory.collatz-bijection using
  ( map-collatz-bijection)
```

### The number of semigroups of order `n` up to isomorphism

OEIS: [A027851](https://oeis.org/A027851)

```agda
open import finite-group-theory.finite-semigroups using
  ( number-of-semigroups-of-order)
```

### The main diagonal of the Ackermann–Péter function

OEIS: [A046859](https://oeis.org/A046859)

```agda
open import elementary-number-theory.ackermann-function using
  ( simplified-ackermann-ℕ)
```

### The number of monoids of order `n` up to isomorphism

OEIS: [A058129](https://oeis.org/A058129)

```agda
open import finite-group-theory.finite-monoids using
  ( number-of-monoids-of-order)
```

## References

{{#bibliography}}
