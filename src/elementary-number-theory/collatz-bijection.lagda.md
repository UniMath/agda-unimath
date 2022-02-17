# The Collatz bijection

```agda
{-# OPTIONS --without-K --exact-split #-}

module elementary-number-theory.collatz-bijection where

open import elementary-number-theory.distance-natural-numbers using (dist-ℕ)
open import elementary-number-theory.euclidean-division-natural-numbers using
  ( quotient-euclidean-division-ℕ)
open import elementary-number-theory.natural-numbers using (ℕ; zero-ℕ; succ-ℕ)
open import elementary-number-theory.modular-arithmetic using (ℤ-Mod; mod-ℕ)
open import elementary-number-theory.multiplication-natural-numbers using
  ( mul-ℕ)

open import foundation.coproduct-types using (inl; inr)
open import foundation.identity-types using (Id; refl)
open import foundation.unit-type using (star)
```

## Idea

We define a bijection of Collatz

## Definition

```agda
cases-map-collatz-bijection : (n : ℕ) (x : ℤ-Mod 3) (p : Id (mod-ℕ 3 n) x) → ℕ
cases-map-collatz-bijection n (inl (inl (inr star))) p =
  quotient-euclidean-division-ℕ 3 (mul-ℕ 2 n)
cases-map-collatz-bijection n (inl (inr star)) p =
  quotient-euclidean-division-ℕ 3 (dist-ℕ (mul-ℕ 4 n) 1)
cases-map-collatz-bijection n (inr star) p =
  quotient-euclidean-division-ℕ 3 (succ-ℕ (mul-ℕ 4 n))

map-collatz-bijection : ℕ → ℕ
map-collatz-bijection n = cases-map-collatz-bijection n (mod-ℕ 3 n) refl
```
