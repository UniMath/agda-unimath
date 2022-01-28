---
title: Univalent Mathematics in Agda
---

# Equality of integers

```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module elementary-number-theory.equality-integers where

open import elementary-number-theory.equality-natural-numbers using
  ( has-decidable-equality-ℕ; Eq-ℕ; refl-Eq-ℕ; eq-Eq-ℕ; is-set-ℕ)
open import elementary-number-theory.integers using
  ( ℤ; zero-ℤ; is-zero-ℤ; one-ℤ; is-one-ℤ; neg-one-ℤ; is-neg-one-ℤ)
open import foundation.coproduct-types using (inl; inr)
open import foundation.decidable-equality using
  ( has-decidable-equality; has-decidable-equality-unit)
open import foundation.decidable-types using (is-decidable)
open import foundation.dependent-pair-types using (pr1; pr2)
open import foundation.empty-types using (empty)
open import foundation.equality-coproduct-types using
  ( has-decidable-equality-coprod; is-set-coprod)
open import foundation.functions using (_∘_)
open import foundation.identity-types using (Id; refl; ap)
open import foundation.sets using (is-set; UU-Set)
open import foundation.unit-type using (unit; star; is-set-unit)
open import foundation.universe-levels using (UU; lzero)
```

### Observational equality on ℤ

```agda
Eq-ℤ : ℤ → ℤ → UU lzero
Eq-ℤ (inl x) (inl y) = Eq-ℕ x y
Eq-ℤ (inl x) (inr y) = empty
Eq-ℤ (inr x) (inl y) = empty
Eq-ℤ (inr (inl x)) (inr (inl y)) = unit
Eq-ℤ (inr (inl x)) (inr (inr y)) = empty
Eq-ℤ (inr (inr x)) (inr (inl y)) = empty
Eq-ℤ (inr (inr x)) (inr (inr y)) = Eq-ℕ x y

refl-Eq-ℤ : (x : ℤ) → Eq-ℤ x x
refl-Eq-ℤ (inl x) = refl-Eq-ℕ x
refl-Eq-ℤ (inr (inl x)) = star
refl-Eq-ℤ (inr (inr x)) = refl-Eq-ℕ x

Eq-eq-ℤ : {x y : ℤ} → Id x y → Eq-ℤ x y
Eq-eq-ℤ {x} {.x} refl = refl-Eq-ℤ x

eq-Eq-ℤ : (x y : ℤ) → Eq-ℤ x y → Id x y
eq-Eq-ℤ (inl x) (inl y) e = ap inl (eq-Eq-ℕ x y e)
eq-Eq-ℤ (inr (inl star)) (inr (inl star)) e = refl
eq-Eq-ℤ (inr (inr x)) (inr (inr y)) e = ap (inr ∘ inr) (eq-Eq-ℕ x y e)
```

# The identity type of the integers

```agda
has-decidable-equality-ℤ : has-decidable-equality ℤ
has-decidable-equality-ℤ =
  has-decidable-equality-coprod
    has-decidable-equality-ℕ
    ( has-decidable-equality-coprod
      has-decidable-equality-unit
      has-decidable-equality-ℕ)

is-decidable-is-zero-ℤ :
  (x : ℤ) → is-decidable (is-zero-ℤ x)
is-decidable-is-zero-ℤ x = has-decidable-equality-ℤ x zero-ℤ

is-decidable-is-one-ℤ :
  (x : ℤ) → is-decidable (is-one-ℤ x)
is-decidable-is-one-ℤ x = has-decidable-equality-ℤ x one-ℤ

is-decidable-is-neg-one-ℤ :
  (x : ℤ) → is-decidable (is-neg-one-ℤ x)
is-decidable-is-neg-one-ℤ x = has-decidable-equality-ℤ x neg-one-ℤ
```

```agda
abstract
  is-set-ℤ : is-set ℤ
  is-set-ℤ = is-set-coprod is-set-ℕ (is-set-coprod is-set-unit is-set-ℕ)

ℤ-Set : UU-Set lzero
pr1 ℤ-Set = ℤ
pr2 ℤ-Set = is-set-ℤ
```
