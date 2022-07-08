---
title: Relatively prime natural numbers
---

```agda
{-# OPTIONS --without-K --exact-split --allow-unsolved-metas #-}

module elementary-number-theory.relatively-prime-natural-numbers where

open import elementary-number-theory.equality-natural-numbers using
  ( is-decidable-is-one-ℕ)
open import elementary-number-theory.greatest-common-divisor-natural-numbers
  using (gcd-ℕ)
open import elementary-number-theory.natural-numbers using
  ( ℕ; zero-ℕ; succ-ℕ; is-one-ℕ; is-set-ℕ)

open import foundation.decidable-propositions using
  ( is-decidable-prop)
open import foundation.decidable-types using (is-decidable)
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.propositions using (is-prop; UU-Prop)
open import foundation.universe-levels using (UU; lzero)
```

## Idea

Two natural numbers `x` and `y` are said to be relatively prime if their greatest common divisor is `1`.

## Definition

```agda
relatively-prime-ℕ : ℕ → ℕ → UU lzero
relatively-prime-ℕ x y = is-one-ℕ (gcd-ℕ x y)
```

## Properties

### Being relatively prime is a proposition

```agda
is-prop-relatively-prime-ℕ : (x y : ℕ) → is-prop (relatively-prime-ℕ x y)
is-prop-relatively-prime-ℕ x y = is-set-ℕ (gcd-ℕ x y) 1

relatively-prime-ℕ-Prop : ℕ → ℕ → UU-Prop lzero
pr1 (relatively-prime-ℕ-Prop x y) = relatively-prime-ℕ x y
pr2 (relatively-prime-ℕ-Prop x y) = is-prop-relatively-prime-ℕ x y
```

### Being relatively prime is decidable

```agda
is-decidable-relatively-prime-ℕ :
  (x y : ℕ) → is-decidable (relatively-prime-ℕ x y)
is-decidable-relatively-prime-ℕ x y = is-decidable-is-one-ℕ (gcd-ℕ x y)

is-decidable-prop-relatively-prime-ℕ :
  (x y : ℕ) → is-decidable-prop (relatively-prime-ℕ x y)
pr1 (is-decidable-prop-relatively-prime-ℕ x y) =
  is-prop-relatively-prime-ℕ x y
pr2 (is-decidable-prop-relatively-prime-ℕ x y) =
  is-decidable-relatively-prime-ℕ x y
```

### A number y is relatively prime to x if and only if `[y] mod x` is a unit in `ℤ-Mod x`

```agda
-- relatively-prime-is-unit-mod-ℕ :
--   (x y : ℕ) → is-unit-ℤ-Mod x (mod-ℕ y) → relatively-prime-ℕ x y
-- relatively-prime-is-unit-mod-ℕ x y H = ?
