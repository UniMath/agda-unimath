# Sequences of the online encyclopedia of integer sequences

This file records formalized sequences of the
[Online Encyclopedia of Integer Sequences](https://oeis.org) {{#cite oeis}}.

```agda
open import foundation.function-extensionality-axiom

module
  literature.oeis
  (funext : function-extensionality)
  where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.exponentiation-natural-numbers funext
open import elementary-number-theory.natural-numbers

open import foundation.function-types funext
```

</details>

## Sequences

### [A000001](https://oeis.org/A000001) The number of groups of order `n`

```agda
open import finite-group-theory.finite-groups funext using
  ( number-of-groups-of-order)
```

### [A000002](https://oeis.org/A000002) The Kolakoski sequence

```agda
open import elementary-number-theory.kolakoski-sequence funext using
  ( kolakoski)
```

### [A000004](https://oeis.org/A000004) The zero sequence

```agda
A000004 : ℕ → ℕ
A000004 _ = zero-ℕ
```

### [A000007](https://oeis.org/A000007) The characteristic function for 0

```agda
A000007 : ℕ → ℕ
A000007 zero-ℕ = 1
A000007 (succ-ℕ _) = 0
```

### [A000010](https://oeis.org/A000010) Euler's totient function

```agda
open import elementary-number-theory.eulers-totient-function funext using
  ( eulers-totient-function-relatively-prime)
```

### [A000012](https://oeis.org/A000012) All 1's sequence

```agda
A000012 : ℕ → ℕ
A000012 _ = 1
```

### [A000027](https://oeis.org/A000027) The positive integers

```agda
A000027 : ℕ → ℕ
A000027 = succ-ℕ
```

### [A000040](https://oeis.org/A000040) The prime numbers

```agda
open import elementary-number-theory.infinitude-of-primes funext using
  ( prime-ℕ)
```

### [A000045](https://oeis.org/A000045) The Fibonacci sequence

```agda
open import elementary-number-theory.fibonacci-sequence funext using
  ( Fibonacci-ℕ)
```

### [A000058](https://oeis.org/A000058) Sylvester's sequence

```agda
open import elementary-number-theory.sylvesters-sequence funext using
  ( sylvesters-sequence-ℕ)
```

### [A000079](https://oeis.org/A000079) Powers of `2`

```agda
A000079 : ℕ → ℕ
A000079 = exp-ℕ 2
```

### [A000108](https://oeis.org/A000108) The Catalan numbers

```agda
open import elementary-number-theory.catalan-numbers funext using
  ( catalan-numbers)
```

### [A000110](https://oeis.org/A000110) The Bell numbers

```agda
open import elementary-number-theory.bell-numbers funext using
  ( bell-number-ℕ)
```

### [A000142](https://oeis.org/A000142) Factorials

```agda
open import elementary-number-theory.factorials funext using
  ( factorial-ℕ)
```

### [A000215](https://oeis.org/A000215) The Fermat numbers

```agda
open import elementary-number-theory.fermat-numbers funext using
  ( fermat-number-ℕ)
```

### [A000244](https://oeis.org/A000244) Powers of `3`

```agda
A000244 : ℕ → ℕ
A000244 = exp-ℕ 3
```

### [A000720](https://oeis.org/A000720) The prime counting function

`open import elementary-number-theory.infinitude-of-primes funext using
 using
  ( prime-counting-ℕ)
```

### [A000945](https://oeis.org/A000945) The Euclid–Mullin sequence

```agda
open import elementary-number-theory.euclid-mullin-sequence funext using
  ( euclid-mullin-ℕ)
```

### [A001175](https://oeis.org/A001175) Pisano periods

```agda
open import elementary-number-theory.pisano-periods funext using
  ( pisano-period)
```

### [A001177](https://oeis.org/A001177) The cofibonacci sequence

```agda
open import elementary-number-theory.cofibonacci funext using
  ( cofibonacci)
```

### [A001477](https://oeis.org/A001477) The natural numbers

```agda
A001477 : ℕ → ℕ
A001477 = id
```

### [A003090](https://oeis.org/A003090) The number of main classes of Latin squares of order `n`

```agda
open import univalent-combinatorics.main-classes-of-latin-squares funext using
  ( number-of-main-classes-of-Latin-squares-of-order)
```

### [A006369](https://oeis.org/A006369) Collatz' bijection

```agda
open import elementary-number-theory.collatz-bijection funext using
  ( map-collatz-bijection)
```

### [A027851](https://oeis.org/A027851) The number of semigroups of order `n` up to isomorphism

```agda
open import finite-group-theory.finite-semigroups funext using
  ( number-of-semigroups-of-order)
```

### [A046859](https://oeis.org/A046859) The main diagonal of the Ackermann–Péter function

```agda
open import elementary-number-theory.ackermann-function using
  ( simplified-ackermann-ℕ)
```

### [A058129](https://oeis.org/A058129) The number of monoids of order `n` up to isomorphism

```agda
open import finite-group-theory.finite-monoids funext using
  ( number-of-monoids-of-order)
```

## References

{{#bibliography}}
