---
title: Euclidean division on the natural numbers
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module elementary-number-theory.euclidean-division-natural-numbers where

open import elementary-number-theory.addition-natural-numbers using
  ( add-ℕ; add-ℕ'; left-unit-law-add-ℕ)
open import elementary-number-theory.congruence-natural-numbers using
  ( cong-ℕ; refl-cong-ℕ; symm-cong-ℕ)
open import elementary-number-theory.distance-natural-numbers using
  ( dist-ℕ; symmetric-dist-ℕ; is-difference-dist-ℕ')
open import elementary-number-theory.inequality-natural-numbers using (le-ℕ)
open import
  elementary-number-theory.modular-arithmetic-standard-finite-types using
  ( mod-succ-ℕ; cong-nat-mod-succ-ℕ; leq-nat-mod-succ-ℕ)
open import elementary-number-theory.multiplication-natural-numbers using
  ( mul-ℕ; right-zero-law-mul-ℕ)
open import elementary-number-theory.natural-numbers using
  ( ℕ; zero-ℕ; succ-ℕ; is-nonzero-ℕ)
open import foundation.cartesian-product-types using (_×_)
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.empty-types using (ex-falso)
open import foundation.identity-types using (_＝_; refl; _∙_; inv; ap)

open import univalent-combinatorics.standard-finite-types using
  ( nat-Fin; strict-upper-bound-nat-Fin)
```

## Idea

Euclidean division is division with remainder, i.e., the Euclidean division of `n` by `d` is the largest natural number `k ≤ n/d`, and the remainder is the unique natural number `r < d` such that `kd + r = n`.

## Definitions

### Euclidean division via sequences

The following definition produces for each `k : ℕ` a sequence of sequences as follows:

```md
       This is the k-th column
        ↓
  0,…,0,0,0,0,0,0,0,…  -- The first sequence is the constant sequence of zeroes
  1,0,…,0,0,0,0,0,0,…  -- We append 1's at the start
        ⋮
  1,…,1,0,…,0,0,0,0,…  -- This is the k-th row    
  2,1,…,1,0,0,0,0,0,…  -- After k steps we append 2's at the start
        ⋮
  2,…,2,1,…,1,0,…,0,…  -- This is the 2k-th row 
  3,2,…,2,1,…,1,0,0,…  -- After another k steps we append 3's at the start
        ⋮
```

This produces an array of natural numbers. We find the euclidean division of `n` by `k+1` in the `k`-th column of the `n`-th row of this array.

```agda
sequence-euclidean-division-ℕ : ℕ → ℕ → ℕ → ℕ
sequence-euclidean-division-ℕ k zero-ℕ m = zero-ℕ
sequence-euclidean-division-ℕ k (succ-ℕ n) zero-ℕ =
  succ-ℕ (sequence-euclidean-division-ℕ k n k)
sequence-euclidean-division-ℕ k (succ-ℕ n) (succ-ℕ m) =
  sequence-euclidean-division-ℕ k n m

euclidean-division-ℕ' : ℕ → ℕ → ℕ
euclidean-division-ℕ' zero-ℕ n = zero-ℕ
euclidean-division-ℕ' (succ-ℕ k) n = sequence-euclidean-division-ℕ k n k  
```

### Euclidean division via modular arithmetic

```agda
euclidean-division-ℕ :
  (k x : ℕ) → Σ ℕ (λ r → (cong-ℕ k x r) × (is-nonzero-ℕ k → le-ℕ r k))
pr1 (euclidean-division-ℕ zero-ℕ x) = x
pr1 (pr2 (euclidean-division-ℕ zero-ℕ x)) = refl-cong-ℕ zero-ℕ x
pr2 (pr2 (euclidean-division-ℕ zero-ℕ x)) f = ex-falso (f refl)
pr1 (euclidean-division-ℕ (succ-ℕ k) x) = nat-Fin (succ-ℕ k) (mod-succ-ℕ k x)
pr1 (pr2 (euclidean-division-ℕ (succ-ℕ k) x)) =
  symm-cong-ℕ
    ( succ-ℕ k)
    ( nat-Fin (succ-ℕ k) (mod-succ-ℕ k x))
    ( x)
    ( cong-nat-mod-succ-ℕ k x)
pr2 (pr2 (euclidean-division-ℕ (succ-ℕ k) x)) f =
  strict-upper-bound-nat-Fin (succ-ℕ k) (mod-succ-ℕ k x)

remainder-euclidean-division-ℕ : ℕ → ℕ → ℕ
remainder-euclidean-division-ℕ k x =
  pr1 (euclidean-division-ℕ k x)

cong-euclidean-division-ℕ :
  (k x : ℕ) → cong-ℕ k x (remainder-euclidean-division-ℕ k x)
cong-euclidean-division-ℕ k x =
  pr1 (pr2 (euclidean-division-ℕ k x))

strict-upper-bound-remainder-euclidean-division-ℕ :
  (k x : ℕ) → is-nonzero-ℕ k → le-ℕ (remainder-euclidean-division-ℕ k x) k
strict-upper-bound-remainder-euclidean-division-ℕ k x =
  pr2 (pr2 (euclidean-division-ℕ k x))

quotient-euclidean-division-ℕ : ℕ → ℕ → ℕ
quotient-euclidean-division-ℕ k x =
  pr1 (cong-euclidean-division-ℕ k x)

eq-quotient-euclidean-division-ℕ :
  (k x : ℕ) →
  ( mul-ℕ (quotient-euclidean-division-ℕ k x) k) ＝
  ( dist-ℕ x (remainder-euclidean-division-ℕ k x))
eq-quotient-euclidean-division-ℕ k x =
  pr2 (cong-euclidean-division-ℕ k x)

eq-euclidean-division-ℕ :
  (k x : ℕ) →
  ( add-ℕ
    ( mul-ℕ (quotient-euclidean-division-ℕ k x) k)
    ( remainder-euclidean-division-ℕ k x)) ＝
  ( x)
eq-euclidean-division-ℕ zero-ℕ x =
  ( inv
    ( ap
      ( add-ℕ' x)
      ( right-zero-law-mul-ℕ (quotient-euclidean-division-ℕ zero-ℕ x)))) ∙
  ( left-unit-law-add-ℕ x)
eq-euclidean-division-ℕ (succ-ℕ k) x =
  ( ap ( add-ℕ' (remainder-euclidean-division-ℕ (succ-ℕ k) x))
       ( ( pr2 (cong-euclidean-division-ℕ (succ-ℕ k) x)) ∙
         ( symmetric-dist-ℕ x
           ( remainder-euclidean-division-ℕ (succ-ℕ k) x)))) ∙
  ( is-difference-dist-ℕ' (remainder-euclidean-division-ℕ (succ-ℕ k) x) x
    ( leq-nat-mod-succ-ℕ k x))
```

```agda
map-extended-euclidean-algorithm : ℕ × ℕ → ℕ × ℕ
pr1 (map-extended-euclidean-algorithm (pair x y)) = y
pr2 (map-extended-euclidean-algorithm (pair x y)) =
  remainder-euclidean-division-ℕ y x
```
