# Euler's totient function

```agda
{-# OPTIONS --without-K --exact-split --allow-unsolved-metas #-}

module elementary-number-theory.eulers-totient-function where

open import elementary-number-theory.natural-numbers using (ℕ)
open import elementary-number-theory.relatively-prime-natural-numbers using
  ( relatively-prime-ℕ; is-decidable-relatively-prime-ℕ)
open import elementary-number-theory.sums-of-natural-numbers using
  ( bounded-sum-ℕ)

open import foundation.coproduct-types using (inl; inr)
open import foundation.decidable-types using (is-decidable)
```

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
