# The Collatz conjecture

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module elementary-number-theory.collatz-conjecture
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.modular-arithmetic-standard-finite-types funext univalence truncations
open import elementary-number-theory.multiplication-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.coproduct-types funext univalence truncations
open import foundation.dependent-pair-types
open import foundation.universe-levels
```

</details>

## Statement

```agda
collatz : ℕ → ℕ
collatz n with is-decidable-div-ℕ 2 n
... | inl (pair y p) = y
... | inr f = succ-ℕ (3 *ℕ n)

iterate-collatz : ℕ → ℕ → ℕ
iterate-collatz zero-ℕ n = n
iterate-collatz (succ-ℕ k) n = collatz (iterate-collatz k n)

Collatz-conjecture : UU lzero
Collatz-conjecture =
  (n : ℕ) → is-nonzero-ℕ n → Σ ℕ (λ k → is-one-ℕ (iterate-collatz k n))
```
