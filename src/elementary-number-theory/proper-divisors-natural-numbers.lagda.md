---
title: Proper divisors of natural numbers
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module elementary-number-theory.proper-divisors-natural-numbers where

open import elementary-number-theory.divisibility-natural-numbers using
  ( div-ℕ; div-zero-ℕ; leq-div-ℕ; is-prop-div-ℕ; is-zero-div-zero-ℕ;
    is-one-div-one-ℕ)
open import elementary-number-theory.equality-natural-numbers using
  ( has-decidable-equality-ℕ)
open import elementary-number-theory.inequality-natural-numbers using
  ( le-ℕ; le-leq-neq-ℕ)
open import
  elementary-number-theory.modular-arithmetic-standard-finite-types using
  ( is-decidable-div-ℕ)
open import elementary-number-theory.multiplication-natural-numbers using
  ( right-unit-law-mul-ℕ)
open import elementary-number-theory.natural-numbers using
  ( ℕ; zero-ℕ; succ-ℕ; is-nonzero-succ-ℕ; is-nonzero-ℕ)
  
open import foundation.cartesian-product-types using (_×_)
open import foundation.decidable-types using
  ( is-decidable; is-decidable-prod; is-decidable-neg)
open import foundation.dependent-pair-types using (pair; pr1; pr2)
open import foundation.empty-types using (ex-falso)
open import foundation.identity-types using (_＝_; refl; inv)
open import foundation.negation using (¬; is-prop-neg)
open import foundation.propositions using
  ( is-prop; is-prop-prod)
open import foundation.universe-levels using (UU; lzero)
```

## Idea

 A proper divisor of a natural number `n` is a natural number `d ≠ n` that divides `n`.

```agda
is-proper-divisor-ℕ : ℕ → ℕ → UU lzero
is-proper-divisor-ℕ n d = ¬ (d ＝ n) × div-ℕ d n

is-decidable-is-proper-divisor-ℕ :
  (n d : ℕ) → is-decidable (is-proper-divisor-ℕ n d)
is-decidable-is-proper-divisor-ℕ n d =
  is-decidable-prod
    ( is-decidable-neg (has-decidable-equality-ℕ d n))
    ( is-decidable-div-ℕ d n)

is-proper-divisor-zero-succ-ℕ : (n : ℕ) → is-proper-divisor-ℕ zero-ℕ (succ-ℕ n)
pr1 (is-proper-divisor-zero-succ-ℕ n) = is-nonzero-succ-ℕ n
pr2 (is-proper-divisor-zero-succ-ℕ n) = div-zero-ℕ (succ-ℕ n)

le-is-proper-divisor-ℕ :
  (x y : ℕ) → is-nonzero-ℕ y → is-proper-divisor-ℕ y x → le-ℕ x y
le-is-proper-divisor-ℕ x y H K =
  le-leq-neq-ℕ (leq-div-ℕ x y H (pr2 K)) (pr1 K)
```

## Properties

### Being a proper divisor is a property

```agda
is-prop-is-proper-divisor-ℕ : (n d : ℕ) → is-prop (is-proper-divisor-ℕ n d)
is-prop-is-proper-divisor-ℕ n zero-ℕ (pair f g) =
  ex-falso (f (inv (is-zero-div-zero-ℕ n g)))
is-prop-is-proper-divisor-ℕ n (succ-ℕ d) =
  is-prop-prod is-prop-neg (is-prop-div-ℕ (succ-ℕ d) n (is-nonzero-succ-ℕ d))
```

### If a natural number has a proper divisor, then `1` is a proper divisor

```agda
is-proper-divisor-one-is-proper-divisor-ℕ :
  {n x : ℕ} → is-proper-divisor-ℕ n x → is-proper-divisor-ℕ n 1
pr1 (is-proper-divisor-one-is-proper-divisor-ℕ {.1} {x} H) refl =
  pr1 H (is-one-div-one-ℕ x (pr2 H))
pr1 (pr2 (is-proper-divisor-one-is-proper-divisor-ℕ {n} {x} H)) = n
pr2 (pr2 (is-proper-divisor-one-is-proper-divisor-ℕ {n} {x} H)) =
  right-unit-law-mul-ℕ n
```
