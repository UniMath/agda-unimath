# The Twin Prime conjecture

```agda
open import foundation.function-extensionality-axiom

module
  elementary-number-theory.twin-prime-conjecture
  (funext : function-extensionality)
  where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.inequality-natural-numbers funext
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.prime-numbers funext

open import foundation.cartesian-product-types funext
open import foundation.dependent-pair-types
open import foundation.universe-levels
```

</details>

## Statement

The twin prime conjecture asserts that there are infinitely many twin primes. We
assert that there are infinitely twin primes by asserting that for every n : ℕ
there is a twin prime that is larger than n.

```agda
is-twin-prime-ℕ : ℕ → UU lzero
is-twin-prime-ℕ n = (is-prime-ℕ n) × (is-prime-ℕ (succ-ℕ (succ-ℕ n)))

twin-prime-conjecture : UU lzero
twin-prime-conjecture =
  (n : ℕ) → Σ ℕ (λ p → (is-twin-prime-ℕ p) × (leq-ℕ n p))
```
