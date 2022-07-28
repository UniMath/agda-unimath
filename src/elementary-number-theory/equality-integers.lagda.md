---
title: Equality of integers
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module elementary-number-theory.equality-integers where

open import elementary-number-theory.equality-natural-numbers using
  ( has-decidable-equality-ℕ)
open import elementary-number-theory.integers using
  ( ℤ; zero-ℤ; is-zero-ℤ; one-ℤ; is-one-ℤ; neg-one-ℤ; is-neg-one-ℤ; ℤ-Set)
open import elementary-number-theory.natural-numbers using
  ( Eq-ℕ; refl-Eq-ℕ; eq-Eq-ℕ; is-set-ℕ; is-prop-Eq-ℕ)

open import foundation.contractible-types using (is-contr)
open import foundation.coproduct-types using (inl; inr)
open import foundation.decidable-equality using
  ( has-decidable-equality; has-decidable-equality-unit;
    has-decidable-equality-coprod)
open import foundation.decidable-types using (is-decidable)
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.empty-types using (empty; is-prop-empty)
open import foundation.equality-coproduct-types using
  ( is-set-coprod)
open import foundation.equality-dependent-pair-types using (eq-pair-Σ)
open import foundation.equivalences using (_≃_; is-equiv)
open import foundation.functions using (_∘_)
open import foundation.fundamental-theorem-of-identity-types using
  ( fundamental-theorem-id)
open import foundation.identity-types using (_＝_; refl; ap)
open import foundation.propositions using (is-prop; eq-is-prop)
open import foundation.set-truncations using
  ( type-trunc-Set; equiv-unit-trunc-Set)
open import foundation.sets using (is-set; UU-Set)
open import foundation.unit-type using (unit; star; is-set-unit; is-prop-unit)
open import foundation.universe-levels using (UU; lzero)
```

## Idea

An equality predicate is defined by pattern matching on the integers. Then we show that this predicate characterizes the identit type of the integers

## Definition

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

Eq-eq-ℤ : {x y : ℤ} → x ＝ y → Eq-ℤ x y
Eq-eq-ℤ {x} {.x} refl = refl-Eq-ℤ x

eq-Eq-ℤ : (x y : ℤ) → Eq-ℤ x y → x ＝ y
eq-Eq-ℤ (inl x) (inl y) e = ap inl (eq-Eq-ℕ x y e)
eq-Eq-ℤ (inr (inl star)) (inr (inl star)) e = refl
eq-Eq-ℤ (inr (inr x)) (inr (inr y)) e = ap (inr ∘ inr) (eq-Eq-ℕ x y e)
```

## Properties

### Equality on the integers is decidable

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

### The type of integers is its own set truncation

```agda
equiv-unit-trunc-ℤ-Set : ℤ ≃ type-trunc-Set ℤ
equiv-unit-trunc-ℤ-Set = equiv-unit-trunc-Set ℤ-Set
```

### Equality on the integers is a proposition

```agda
is-prop-Eq-ℤ :
  (x y : ℤ) → is-prop (Eq-ℤ x y)
is-prop-Eq-ℤ (inl x) (inl y) = is-prop-Eq-ℕ x y
is-prop-Eq-ℤ (inl x) (inr y) = is-prop-empty
is-prop-Eq-ℤ (inr x) (inl x₁) = is-prop-empty
is-prop-Eq-ℤ (inr (inl x)) (inr (inl y)) = is-prop-unit
is-prop-Eq-ℤ (inr (inl x)) (inr (inr y)) = is-prop-empty
is-prop-Eq-ℤ (inr (inr x)) (inr (inl y)) = is-prop-empty
is-prop-Eq-ℤ (inr (inr x)) (inr (inr y)) = is-prop-Eq-ℕ x y

Eq-ℤ-eq :
  {x y : ℤ} → x ＝ y → Eq-ℤ x y
Eq-ℤ-eq {x} {.x} refl = refl-Eq-ℤ x

contraction-total-Eq-ℤ :
  (x : ℤ) (y : Σ ℤ (Eq-ℤ x)) → pair x (refl-Eq-ℤ x) ＝ y
contraction-total-Eq-ℤ (inl x) (pair (inl y) e) =
  eq-pair-Σ
    ( ap inl (eq-Eq-ℕ x y e))
    ( eq-is-prop (is-prop-Eq-ℕ x y))
contraction-total-Eq-ℤ (inr (inl star)) (pair (inr (inl star)) e) =
  eq-pair-Σ refl (eq-is-prop is-prop-unit)
contraction-total-Eq-ℤ (inr (inr x)) (pair (inr (inr y)) e) =
  eq-pair-Σ
    ( ap (inr ∘ inr) (eq-Eq-ℕ x y e))
    ( eq-is-prop (is-prop-Eq-ℕ x y))

is-contr-total-Eq-ℤ :
  (x : ℤ) → is-contr (Σ ℤ (Eq-ℤ x))
is-contr-total-Eq-ℤ x =
  pair (pair x (refl-Eq-ℤ x)) (contraction-total-Eq-ℤ x)

is-equiv-Eq-ℤ-eq :
  (x y : ℤ) → is-equiv (Eq-ℤ-eq {x} {y})
is-equiv-Eq-ℤ-eq x =
  fundamental-theorem-id
    ( is-contr-total-Eq-ℤ x)
    ( λ y → Eq-ℤ-eq {x} {y})
```
