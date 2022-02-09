---
title: Univalent Mathematics in Agda
---

# Equality on the standard finite types

```agda
{-# OPTIONS --without-K --exact-split #-}

module elementary-number-theory.equality-standard-finite-types where

open import elementary-number-theory.natural-numbers using (ℕ; zero-ℕ; succ-ℕ)
open import elementary-number-theory.standard-finite-types using
  ( Fin; zero-Fin; is-zero-Fin; one-Fin; is-one-Fin; neg-one-Fin;
    is-neg-one-Fin; is-zero-or-one-Fin-two-ℕ)
open import foundation.contractible-types using (is-contr)
open import foundation.coproduct-types using (coprod; inl; inr; is-prop-coprod)
open import foundation.decidable-types using
  ( is-decidable; is-decidable-empty; is-decidable-unit)
open import foundation.dependent-pair-types using (pr1; pr2)
open import foundation.empty-types using (empty; is-set-empty)
open import foundation.equality-coproduct-types using
  ( is-set-coprod)
open import foundation.functoriality-coproduct-types using (map-coprod)
open import foundation.identity-types using (Id; refl; ap; inv; _∙_)
open import foundation.negation using (map-neg)
open import foundation.propositions using (is-prop; is-proof-irrelevant-is-prop)
open import foundation.sets using (is-set; UU-Set)
open import foundation.unit-type using (unit; star; is-set-unit)
open import foundation.universe-levels using (UU; lzero)
```

# Equality of the standard finite types

```agda
Eq-Fin : (k : ℕ) → Fin k → Fin k → UU lzero
Eq-Fin (succ-ℕ k) (inl x) (inl y) = Eq-Fin k x y
Eq-Fin (succ-ℕ k) (inl x) (inr y) = empty
Eq-Fin (succ-ℕ k) (inr x) (inl y) = empty
Eq-Fin (succ-ℕ k) (inr x) (inr y) = unit

refl-Eq-Fin : {k : ℕ} (x : Fin k) → Eq-Fin k x x
refl-Eq-Fin {succ-ℕ k} (inl x) = refl-Eq-Fin x
refl-Eq-Fin {succ-ℕ k} (inr x) = star

Eq-Fin-eq : {k : ℕ} {x y : Fin k} → Id x y → Eq-Fin k x y
Eq-Fin-eq {k} refl = refl-Eq-Fin {k} _

eq-Eq-Fin :
  {k : ℕ} {x y : Fin k} → Eq-Fin k x y → Id x y
eq-Eq-Fin {succ-ℕ k} {inl x} {inl y} e = ap inl (eq-Eq-Fin e)
eq-Eq-Fin {succ-ℕ k} {inr star} {inr star} star = refl

is-decidable-Eq-Fin : (k : ℕ) (x y : Fin k) → is-decidable (Eq-Fin k x y)
is-decidable-Eq-Fin (succ-ℕ k) (inl x) (inl y) = is-decidable-Eq-Fin k x y
is-decidable-Eq-Fin (succ-ℕ k) (inl x) (inr y) = is-decidable-empty
is-decidable-Eq-Fin (succ-ℕ k) (inr x) (inl y) = is-decidable-empty
is-decidable-Eq-Fin (succ-ℕ k) (inr x) (inr y) = is-decidable-unit

has-decidable-equality-Fin :
  {k : ℕ} (x y : Fin k) → is-decidable (Id x y)
has-decidable-equality-Fin {k} x y =
  map-coprod eq-Eq-Fin (map-neg Eq-Fin-eq) (is-decidable-Eq-Fin k x y)

is-decidable-is-zero-Fin :
  {k : ℕ} (x : Fin k) → is-decidable (is-zero-Fin x)
is-decidable-is-zero-Fin {succ-ℕ k} x =
  has-decidable-equality-Fin x zero-Fin

is-decidable-is-neg-one-Fin :
  {k : ℕ} (x : Fin k) → is-decidable (is-neg-one-Fin x)
is-decidable-is-neg-one-Fin {succ-ℕ k} x =
  has-decidable-equality-Fin x neg-one-Fin

is-decidable-is-one-Fin :
  {k : ℕ} (x : Fin k) → is-decidable (is-one-Fin x)
is-decidable-is-one-Fin {succ-ℕ k} x =
  has-decidable-equality-Fin x one-Fin
```

### The standard finite types are sets

```agda
abstract
  is-set-Fin : (n : ℕ) → is-set (Fin n)
  is-set-Fin zero-ℕ = is-set-empty
  is-set-Fin (succ-ℕ n) =
    is-set-coprod (is-set-Fin n) is-set-unit

Fin-Set : (n : ℕ) → UU-Set lzero
pr1 (Fin-Set n) = Fin n
pr2 (Fin-Set n) = is-set-Fin n
```

### Being zero or being one is a proposition

```agda
is-prop-is-zero-Fin :
  {k : ℕ} (x : Fin (succ-ℕ k)) → is-prop (is-zero-Fin x)
is-prop-is-zero-Fin {k} x = is-set-Fin (succ-ℕ k) x zero-Fin

is-prop-is-one-Fin :
  {k : ℕ} (x : Fin (succ-ℕ k)) → is-prop (is-one-Fin x)
is-prop-is-one-Fin {k} x = is-set-Fin (succ-ℕ k) x one-Fin

is-prop-is-zero-or-one-Fin-two-ℕ :
  (x : Fin 2) → is-prop (coprod (is-zero-Fin x) (is-one-Fin x))
is-prop-is-zero-or-one-Fin-two-ℕ x =
  is-prop-coprod
    ( λ p q → Eq-Fin-eq (inv p ∙ q))
    ( is-prop-is-zero-Fin x)
    ( is-prop-is-one-Fin x)
```

### Every element in the standard two-element type is either 0 or 1.

```agda
is-contr-is-zero-or-one-Fin-two-ℕ :
  (x : Fin 2) → is-contr (coprod (is-zero-Fin x) (is-one-Fin x))
is-contr-is-zero-or-one-Fin-two-ℕ x =
  is-proof-irrelevant-is-prop
    ( is-prop-is-zero-or-one-Fin-two-ℕ x)
    ( is-zero-or-one-Fin-two-ℕ x)
```
