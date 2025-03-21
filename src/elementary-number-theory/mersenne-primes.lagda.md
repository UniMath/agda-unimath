# Mersenne primes

```agda
module elementary-number-theory.mersenne-primes where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.distance-natural-numbers
open import elementary-number-theory.exponentiation-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.prime-numbers

open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.universe-levels
```

</details>

## Idea

A Mersenne prime is a prime number that is one less than a power of two.

## Definition

```agda
is-mersenne-prime : ℕ → UU lzero
is-mersenne-prime n = is-prime-ℕ n × Σ ℕ (λ k → dist-ℕ (exp-ℕ 2 k) 1 ＝ n)

is-mersenne-prime-power : ℕ → UU lzero
is-mersenne-prime-power k = is-prime-ℕ (dist-ℕ (exp-ℕ 2 k) 1)
```
