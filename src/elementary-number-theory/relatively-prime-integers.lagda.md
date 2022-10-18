---
title: Relatively prime integers
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module elementary-number-theory.relatively-prime-integers where

open import elementary-number-theory.integers using
  ( ℤ; is-one-ℤ; is-set-ℤ; one-ℤ)
open import elementary-number-theory.greatest-common-divisor-integers using
  ( gcd-ℤ)

open import foundation.universe-levels using (UU; lzero)
open import foundation.propositions using (is-prop)
```

## Idea

Two integers are said to be relatively prime if their greatest common divisor is 1.

## Definition

```agda
is-relative-prime-ℤ : ℤ → ℤ → UU lzero
is-relative-prime-ℤ x y = is-one-ℤ (gcd-ℤ x y)
```

## Properties

```agda
is-prop-is-relative-prime-ℤ : (x y : ℤ) → is-prop (is-relative-prime-ℤ x y)
is-prop-is-relative-prime-ℤ x y = is-set-ℤ (gcd-ℤ x y) one-ℤ
```
