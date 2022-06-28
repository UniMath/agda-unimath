---
title: The divisibility relation on the standard finite types
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module elementary-number-theory.divisibility-standard-finite-types where

open import
  elementary-number-theory.modular-arithmetic-standard-finite-types using
  ( mul-Fin; left-unit-law-mul-Fin; associative-mul-Fin; left-zero-law-mul-Fin;
    right-unit-law-mul-Fin; right-zero-law-mul-Fin)
open import elementary-number-theory.natural-numbers using (ℕ; zero-ℕ; succ-ℕ)

open import foundation.decidable-types using (is-decidable)
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.identity-types using (_＝_; _∙_; ap; inv)
open import foundation.universe-levels using (UU; lzero)

open import univalent-combinatorics.decidable-dependent-pair-types using
  ( is-decidable-Σ-Fin)
open import univalent-combinatorics.equality-standard-finite-types using
  ( has-decidable-equality-Fin)
open import univalent-combinatorics.standard-finite-types using
  ( Fin; one-Fin; zero-Fin; is-zero-Fin)
```

## Idea

Given two elements `x y : Fin k`, we say that `x` divides `y` if there is an element `u : Fin k` such that `mul-Fin u x = y`.

## Definition

```agda
div-Fin : {k : ℕ} → Fin k → Fin k → UU lzero
div-Fin {k} x y = Σ (Fin k) (λ u → mul-Fin u x ＝ y)
```

## Properties

### The divisibility relation is reflexive

```agda
refl-div-Fin : {k : ℕ} (x : Fin k) → div-Fin x x
pr1 (refl-div-Fin {succ-ℕ k} x) = one-Fin
pr2 (refl-div-Fin {succ-ℕ k} x) = left-unit-law-mul-Fin x
```

### The divisibility relation is transitive

```agda
trans-div-Fin :
  {k : ℕ} (x y z : Fin k) → div-Fin x y → div-Fin y z → div-Fin x z
pr1 (trans-div-Fin x y z (pair u p) (pair v q)) = mul-Fin v u
pr2 (trans-div-Fin x y z (pair u p) (pair v q)) =
  associative-mul-Fin v u x ∙ (ap (mul-Fin v) p ∙ q)
```

### Every element divides zero

```agda
div-zero-Fin : {k : ℕ} (x : Fin (succ-ℕ k)) → div-Fin x zero-Fin
pr1 (div-zero-Fin x) = zero-Fin
pr2 (div-zero-Fin x) = left-zero-law-mul-Fin x
```

### Every element is divisible by one

```agda
div-one-Fin : {k : ℕ} (x : Fin (succ-ℕ k)) → div-Fin one-Fin x
pr1 (div-one-Fin x) = x
pr2 (div-one-Fin x) = right-unit-law-mul-Fin x
```

### The only element that is divisible by zero is zero itself

```agda
is-zero-div-zero-Fin :
  {k : ℕ} (x : Fin (succ-ℕ k)) → div-Fin zero-Fin x → is-zero-Fin x
is-zero-div-zero-Fin {k} x (pair u p) = inv p ∙ right-zero-law-mul-Fin u
```

### The divisibility relation is decidable

```agda
is-decidable-div-Fin : {k : ℕ} (x y : Fin k) → is-decidable (div-Fin x y)
is-decidable-div-Fin x y =
  is-decidable-Σ-Fin (λ u → has-decidable-equality-Fin (mul-Fin u x) y)
```
