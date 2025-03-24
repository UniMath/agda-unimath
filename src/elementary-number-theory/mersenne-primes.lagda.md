# Mersenne primes

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module elementary-number-theory.mersenne-primes
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.distance-natural-numbers funext univalence truncations
open import elementary-number-theory.exponentiation-natural-numbers funext univalence truncations
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.prime-numbers funext univalence truncations

open import foundation.cartesian-product-types funext univalence
open import foundation.dependent-pair-types
open import foundation.identity-types funext
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
