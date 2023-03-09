# Euler's totient function

```agda
module elementary-number-theory.eulers-totient-function where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.relatively-prime-natural-numbers
open import elementary-number-theory.sums-of-natural-numbers

open import foundation.coproduct-types
open import foundation.decidable-types
```

</details>

## Idea

Euler's totient function `φ : ℕ → ℕ` is the function that maps a natural number `n` to the number of `x < n` that are relatively prime with `n`.

## Definition

```agda
eulers-totient-function : ℕ → ℕ
eulers-totient-function n =
  bounded-sum-ℕ n (λ x H → α x)
  where
  α' : (x : ℕ) → is-decidable (relatively-prime-ℕ x n) → ℕ
  α' x (inl H) = 1
  α' x (inr H) = 0
  α : ℕ → ℕ
  α x = α' x (is-decidable-relatively-prime-ℕ x n)
```
