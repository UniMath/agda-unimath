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

A {{#concept "Mersenne prime" Agda=is-mersenne-prime-ℕ}} is a prime number that is one less than a power of two.

## Definitions

### The Mersenne numbers

```agda
mersenne-number-ℕ : ℕ → ℕ
mersenne-number-ℕ = ?
```

### The predicate of being a Mersenne prime

```agda
is-mersenne-prime-ℕ : ℕ → UU lzero
is-mersenne-prime-ℕ n = is-prime-ℕ n × Σ ℕ (λ k → dist-ℕ (exp-ℕ 2 k) 1 ＝ n)

is-mersenne-prime-power-ℕ : ℕ → UU lzero
is-mersenne-prime-power-ℕ k = is-prime-ℕ (dist-ℕ (exp-ℕ 2 k) 1)
```
