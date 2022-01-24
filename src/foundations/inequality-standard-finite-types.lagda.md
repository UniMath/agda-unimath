---
title: Univalent Mathematics in Agda
---

```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module foundations.inequality-standard-finite-types where

open import foundations.coproduct-types using (inl; inr)
open import foundations.empty-type using (empty; ex-falso)
open import foundations.identity-types using (Id; refl; ap)
open import foundations.inequality-natural-numbers using
  ( leq-ℕ; leq-le-ℕ; refl-leq-ℕ; contradiction-le-ℕ)
open import foundations.levels using (UU; lzero)
open import foundations.natural-numbers using (ℕ; zero-ℕ; succ-ℕ)
open import foundations.standard-finite-types using
  ( Fin; neg-one-Fin; inl-Fin; succ-Fin; nat-Fin; strict-upper-bound-nat-Fin)
open import foundations.unit-type using (unit; star)
```

# Inequality on the standard finite types

```agda
leq-Fin : {k : ℕ} → Fin k → Fin k → UU lzero
leq-Fin {succ-ℕ k} x (inr y) = unit
leq-Fin {succ-ℕ k} (inl x) (inl y) = leq-Fin x y
leq-Fin {succ-ℕ k} (inr x) (inl y) = empty

leq-neg-one-Fin : {k : ℕ} (x : Fin (succ-ℕ k)) → leq-Fin x neg-one-Fin
leq-neg-one-Fin x = star

refl-leq-Fin : {k : ℕ} (x : Fin k) → leq-Fin x x
refl-leq-Fin {succ-ℕ k} (inl x) = refl-leq-Fin x
refl-leq-Fin {succ-ℕ k} (inr star) = star

antisymmetric-leq-Fin :
  {k : ℕ} {x y : Fin k} → leq-Fin x y → leq-Fin y x → Id x y
antisymmetric-leq-Fin {succ-ℕ k} {inl x} {inl y} H K =
  ap inl (antisymmetric-leq-Fin H K)
antisymmetric-leq-Fin {succ-ℕ k} {inr star} {inr star} H K = refl

transitive-leq-Fin :
  {k : ℕ} {x y z : Fin k} → leq-Fin x y → leq-Fin {k} y z → leq-Fin {k} x z
transitive-leq-Fin {succ-ℕ k} {inl x} {inl y} {inl z} H K =
  transitive-leq-Fin {k} H K
transitive-leq-Fin {succ-ℕ k} {inl x} {inl y} {inr star} H K = star
transitive-leq-Fin {succ-ℕ k} {inl x} {inr star} {inr star} H K = star
transitive-leq-Fin {succ-ℕ k} {inr star} {inr star} {inr star} H K = star

concatenate-eq-leq-eq-Fin :
  {k : ℕ} {x1 x2 x3 x4 : Fin k} →
  Id x1 x2 → leq-Fin x2 x3 → Id x3 x4 → leq-Fin x1 x4
concatenate-eq-leq-eq-Fin refl H refl = H

leq-succ-Fin :
  {k : ℕ} (x : Fin k) → leq-Fin (inl-Fin k x) (succ-Fin (inl-Fin k x))
leq-succ-Fin {succ-ℕ k} (inl x) = leq-succ-Fin x
leq-succ-Fin {succ-ℕ k} (inr star) = star

preserves-leq-nat-Fin :
  {k : ℕ} {x y : Fin k} → leq-Fin x y → leq-ℕ (nat-Fin x) (nat-Fin y)
preserves-leq-nat-Fin {succ-ℕ k} {inl x} {inl y} H =
  preserves-leq-nat-Fin {k} H
preserves-leq-nat-Fin {succ-ℕ k} {inl x} {inr star} H =
  leq-le-ℕ {nat-Fin x} {k} (strict-upper-bound-nat-Fin x)
preserves-leq-nat-Fin {succ-ℕ k} {inr star} {inr star} H =
  refl-leq-ℕ k

reflects-leq-nat-Fin :
  {k : ℕ} {x y : Fin k} → leq-ℕ (nat-Fin x) (nat-Fin y) → leq-Fin x y
reflects-leq-nat-Fin {succ-ℕ k} {inl x} {inl y} H =
  reflects-leq-nat-Fin {k} H
reflects-leq-nat-Fin {succ-ℕ k} {inr star} {inl y} H =
  ex-falso (contradiction-le-ℕ (nat-Fin y) k (strict-upper-bound-nat-Fin y) H)
reflects-leq-nat-Fin {succ-ℕ k} {inl x} {inr star} H = star
reflects-leq-nat-Fin {succ-ℕ k} {inr star} {inr star} H = star
```
