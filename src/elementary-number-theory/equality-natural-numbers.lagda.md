---
title: Equality of natural numbers
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module elementary-number-theory.equality-natural-numbers where

open import elementary-number-theory.natural-numbers using
  ( ℕ; zero-ℕ; succ-ℕ; is-zero-ℕ; is-zero-ℕ'; is-nonzero-ℕ; is-one-ℕ; is-one-ℕ';
    is-not-one-ℕ; Eq-ℕ; eq-Eq-ℕ; Eq-eq-ℕ; is-set-ℕ; refl-Eq-ℕ; ℕ-Set)

open import foundation-core.decidable-propositions using (decidable-Prop)
open import foundation-core.discrete-types using (Discrete-Type)

open import foundation.contractible-types using (is-contr)
open import foundation.coproduct-types using (inl; inr)
open import foundation.decidable-equality using (has-decidable-equality)
open import foundation.decidable-types using
  ( is-decidable; is-decidable-iff; is-decidable-neg)
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.empty-types using (empty; is-prop-empty)
open import foundation.equivalences using (is-equiv; _≃_)
open import foundation.functions using (id)
open import foundation.fundamental-theorem-of-identity-types using
  ( fundamental-theorem-id)
open import foundation.identity-types using (_＝_; refl; ap)
open import foundation.propositions using (is-prop)
open import foundation.set-truncations using
  ( type-trunc-Set; equiv-unit-trunc-Set)
open import foundation.sets using (is-set; is-set-prop-in-id; UU-Set)
open import foundation.unit-type using (unit; star; is-prop-unit)
open import foundation.universe-levels using (UU; lzero)
```

## Properties

### The type of natural numbers has decidable equality

```agda
is-decidable-Eq-ℕ :
  (m n : ℕ) → is-decidable (Eq-ℕ m n)
is-decidable-Eq-ℕ zero-ℕ zero-ℕ = inl star
is-decidable-Eq-ℕ zero-ℕ (succ-ℕ n) = inr id
is-decidable-Eq-ℕ (succ-ℕ m) zero-ℕ = inr id
is-decidable-Eq-ℕ (succ-ℕ m) (succ-ℕ n) = is-decidable-Eq-ℕ m n

has-decidable-equality-ℕ : has-decidable-equality ℕ
has-decidable-equality-ℕ x y =
  is-decidable-iff (eq-Eq-ℕ x y) Eq-eq-ℕ (is-decidable-Eq-ℕ x y)

decidable-eq-ℕ : ℕ → ℕ → decidable-Prop lzero
pr1 (decidable-eq-ℕ m n) = (m ＝ n)
pr1 (pr2 (decidable-eq-ℕ m n)) = is-set-ℕ m n
pr2 (pr2 (decidable-eq-ℕ m n)) = has-decidable-equality-ℕ m n

is-decidable-is-zero-ℕ : (n : ℕ) → is-decidable (is-zero-ℕ n)
is-decidable-is-zero-ℕ n = has-decidable-equality-ℕ n zero-ℕ

is-decidable-is-zero-ℕ' : (n : ℕ) → is-decidable (is-zero-ℕ' n)
is-decidable-is-zero-ℕ' n = has-decidable-equality-ℕ zero-ℕ n

is-decidable-is-nonzero-ℕ : (n : ℕ) → is-decidable (is-nonzero-ℕ n)
is-decidable-is-nonzero-ℕ n =
  is-decidable-neg (is-decidable-is-zero-ℕ n)

is-decidable-is-one-ℕ : (n : ℕ) → is-decidable (is-one-ℕ n)
is-decidable-is-one-ℕ n = has-decidable-equality-ℕ n 1

is-decidable-is-one-ℕ' : (n : ℕ) → is-decidable (is-one-ℕ' n)
is-decidable-is-one-ℕ' n = has-decidable-equality-ℕ 1 n

is-decidable-is-not-one-ℕ :
  (x : ℕ) → is-decidable (is-not-one-ℕ x)
is-decidable-is-not-one-ℕ x =
  is-decidable-neg (is-decidable-is-one-ℕ x)
```

## The full characterization of the identity type of ℕ

```agda
map-total-Eq-ℕ :
  (m : ℕ) → Σ ℕ (Eq-ℕ m) → Σ ℕ (Eq-ℕ (succ-ℕ m))
pr1 (map-total-Eq-ℕ m (pair n e)) = succ-ℕ n
pr2 (map-total-Eq-ℕ m (pair n e)) = e

is-contr-total-Eq-ℕ :
  (m : ℕ) → is-contr (Σ ℕ (Eq-ℕ m))
pr1 (pr1 (is-contr-total-Eq-ℕ m)) = m
pr2 (pr1 (is-contr-total-Eq-ℕ m)) = refl-Eq-ℕ m
pr2 (is-contr-total-Eq-ℕ zero-ℕ) (pair zero-ℕ star) = refl
pr2 (is-contr-total-Eq-ℕ (succ-ℕ m)) (pair (succ-ℕ n) e) =
  ap (map-total-Eq-ℕ m) (pr2 (is-contr-total-Eq-ℕ m) (pair n e))

is-equiv-Eq-eq-ℕ :
  {m n : ℕ} → is-equiv (Eq-eq-ℕ {m} {n})
is-equiv-Eq-eq-ℕ {m} {n} =
  fundamental-theorem-id 
    ( is-contr-total-Eq-ℕ m)
    ( λ y → Eq-eq-ℕ {m} {y})
    ( n)
```

### The type of natural numbers is its own set truncation

```agda
equiv-unit-trunc-ℕ-Set : ℕ ≃ type-trunc-Set ℕ
equiv-unit-trunc-ℕ-Set = equiv-unit-trunc-Set ℕ-Set
```
