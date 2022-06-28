---
title: Unit similarity on the standard finite types
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module elementary-number-theory.unit-similarity-standard-finite-types where

open import elementary-number-theory.congruence-natural-numbers using
  ( cong-ℕ; scalar-invariant-cong-ℕ; symm-cong-ℕ)
open import
  elementary-number-theory.modular-arithmetic-standard-finite-types using
  ( mul-Fin; left-unit-law-mul-Fin; associative-mul-Fin; mul-Fin';
    mod-succ-ℕ; cong-eq-mod-succ-ℕ; eq-mod-succ-cong-ℕ; cong-nat-mod-succ-ℕ)
open import elementary-number-theory.multiplication-natural-numbers using
  ( mul-ℕ)
open import elementary-number-theory.natural-numbers using (ℕ; zero-ℕ; succ-ℕ)
open import elementary-number-theory.unit-elements-standard-finite-types using
  ( unit-Fin; one-unit-Fin; inv-unit-Fin; mul-unit-Fin)

open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.identity-types using (Id; ap; inv; _∙_)
open import foundation.universe-levels using (UU; lzero)

open import univalent-combinatorics.standard-finite-types using
  ( Fin; one-Fin; nat-Fin)
```

## Idea

Two elements `x y : Fin k` are said to be unit similar if there is a unit element `u : Fin k` such that `mul-Fin u x = y`. This relation gives a groupoid structure on `Fin k`.

## Definition

```agda
sim-unit-Fin :
  {k : ℕ} → Fin k → Fin k → UU lzero
sim-unit-Fin {k} x y = Σ (unit-Fin k) (λ u → Id (mul-Fin (pr1 u) x) y)

refl-sim-unit-Fin :
  {k : ℕ} (x : Fin k) → sim-unit-Fin x x
pr1 (refl-sim-unit-Fin {succ-ℕ k} x) = one-unit-Fin
pr2 (refl-sim-unit-Fin {succ-ℕ k} x) = left-unit-law-mul-Fin x

symm-sim-unit-Fin :
  {k : ℕ} (x y : Fin k) → sim-unit-Fin x y → sim-unit-Fin y x
pr1 (symm-sim-unit-Fin {succ-ℕ k} x y (pair (pair u (pair v q)) p)) =
  inv-unit-Fin (pair u (pair v q))
pr2 (symm-sim-unit-Fin {succ-ℕ k} x y (pair (pair u (pair v q)) p)) =
  ( ( ( ap (mul-Fin v) (inv p)) ∙
        ( inv (associative-mul-Fin v u x))) ∙
      ( ap (mul-Fin' x) q)) ∙
    ( left-unit-law-mul-Fin x)

trans-sim-unit-Fin :
  {k : ℕ} (x y z : Fin k) → sim-unit-Fin x y → sim-unit-Fin y z →
  sim-unit-Fin x z
pr1 (trans-sim-unit-Fin {succ-ℕ k} x y z (pair u p) (pair v q)) =
  mul-unit-Fin v u
pr2 (trans-sim-unit-Fin {succ-ℕ k} x y z (pair u p) (pair v q)) =
  associative-mul-Fin (pr1 v) (pr1 u) x ∙ (ap (mul-Fin (pr1 v)) p ∙ q)

is-mod-unit-ℕ : (k x : ℕ) → UU lzero
is-mod-unit-ℕ k x = Σ ℕ (λ l → cong-ℕ k (mul-ℕ l x) 1)

is-mod-unit-sim-unit-mod-succ-ℕ :
  (k x : ℕ) → sim-unit-Fin (mod-succ-ℕ k x) one-Fin → is-mod-unit-ℕ (succ-ℕ k) x
pr1 (is-mod-unit-sim-unit-mod-succ-ℕ k x (pair u p)) =
  nat-Fin (pr1 u)
pr2 (is-mod-unit-sim-unit-mod-succ-ℕ k x (pair u p)) =
  cong-eq-mod-succ-ℕ k
    ( mul-ℕ (nat-Fin (pr1 u)) x)
    ( 1)
    ( ( eq-mod-succ-cong-ℕ k
        ( mul-ℕ (nat-Fin (pr1 u)) x)
        ( mul-ℕ (nat-Fin (pr1 u)) (nat-Fin (mod-succ-ℕ k x)))
        ( scalar-invariant-cong-ℕ
          ( succ-ℕ k)
          ( x)
          ( nat-Fin (mod-succ-ℕ k x))
          ( nat-Fin (pr1 u))
          ( symm-cong-ℕ
            ( succ-ℕ k)
            ( nat-Fin (mod-succ-ℕ k x))
            ( x)
            ( cong-nat-mod-succ-ℕ k x)))) ∙
      ( p))
```

