---
title: Univalent Mathematics in Agda
---

# The classical definition of the finite types

```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module elementary-number-theory.classical-finite-types where

open import elementary-number-theory.congruence-natural-numbers using
  ( eq-cong-le-ℕ)
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.identity-types using (Id; refl)
open import elementary-number-theory.inequality-natural-numbers using (le-ℕ)
open import foundation.levels using (UU; lzero)
open import
  elementary-number-theory.modular-arithmetic-standard-finite-types using
  ( mod-succ-ℕ; issec-nat-Fin; cong-nat-mod-succ-ℕ)
open import elementary-number-theory.natural-numbers using
  ( ℕ; zero-ℕ; succ-ℕ; is-injective-succ-ℕ)
open import elementary-number-theory.standard-finite-types using
  ( Fin; nat-Fin; strict-upper-bound-nat-Fin)
open import foundations.unit-type using (star)
```

# The classical finite types

```agda
classical-Fin : ℕ → UU lzero
classical-Fin k = Σ ℕ (λ x → le-ℕ x k)

nat-classical-Fin : (k : ℕ) → classical-Fin k → ℕ
nat-classical-Fin k = pr1

Eq-classical-Fin : (k : ℕ) (x y : classical-Fin k) → UU lzero
Eq-classical-Fin k x y = Id (nat-classical-Fin k x) (nat-classical-Fin k y)

eq-succ-classical-Fin :
  (k : ℕ) (x y : classical-Fin k) → Id {A = classical-Fin k} x y →
  Id {A = classical-Fin (succ-ℕ k)}
     ( pair (succ-ℕ (pr1 x)) (pr2 x))
     ( pair (succ-ℕ (pr1 y)) (pr2 y))
eq-succ-classical-Fin k x .x refl = refl

eq-Eq-classical-Fin :
  (k : ℕ) (x y : classical-Fin k) → Eq-classical-Fin k x y → Id x y
eq-Eq-classical-Fin (succ-ℕ k) (pair zero-ℕ star) (pair zero-ℕ star) e = refl
eq-Eq-classical-Fin (succ-ℕ k) (pair (succ-ℕ x) p) (pair (succ-ℕ y) q) e =
  eq-succ-classical-Fin k
    ( pair x p)
    ( pair y q)
    ( eq-Eq-classical-Fin k (pair x p) (pair y q) (is-injective-succ-ℕ e))

{- We define maps back and forth between the standard finite sets and the
   bounded natural numbers -}

standard-classical-Fin : {k : ℕ} → classical-Fin k → Fin k
standard-classical-Fin {succ-ℕ k} (pair x H) = mod-succ-ℕ k x

classical-standard-Fin :
  (k : ℕ) → Fin k → classical-Fin k
pr1 (classical-standard-Fin k x) = nat-Fin x
pr2 (classical-standard-Fin k x) = strict-upper-bound-nat-Fin x

{- We show that these maps are mutual inverses -}

issec-classical-standard-Fin :
  {k : ℕ} (x : Fin k) →
  Id (standard-classical-Fin (classical-standard-Fin k x)) x
issec-classical-standard-Fin {succ-ℕ k} x = issec-nat-Fin x

isretr-classical-standard-Fin :
  {k : ℕ} (x : classical-Fin k) →
  Id (classical-standard-Fin k (standard-classical-Fin x)) x
isretr-classical-standard-Fin {succ-ℕ k} (pair x p) =
  eq-Eq-classical-Fin (succ-ℕ k)
    ( classical-standard-Fin (succ-ℕ k) (standard-classical-Fin (pair x p)))
    ( pair x p)
    ( eq-cong-le-ℕ
      ( succ-ℕ k)
      ( nat-Fin (mod-succ-ℕ k x))
      ( x)
      ( strict-upper-bound-nat-Fin (mod-succ-ℕ k x))
      ( p)
      ( cong-nat-mod-succ-ℕ k x))
```
