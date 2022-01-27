---
title: Univalent Mathematics in Agda
---

# Euclidean division on the natural numbers

```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module elementary-number-theory.euclidean-division-natural-numbers where

open import elementary-number-theory.addition-natural-numbers using
  ( add-ℕ; add-ℕ'; left-unit-law-add-ℕ)
open import foundation.cartesian-product-types using (_×_)
open import elementary-number-theory.congruence-natural-numbers using
  ( cong-ℕ; refl-cong-ℕ; symm-cong-ℕ)
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import elementary-number-theory.distance-natural-numbers using
  ( dist-ℕ; symmetric-dist-ℕ; is-difference-dist-ℕ')
open import foundation.empty-type using (ex-falso)
open import foundation.identity-types using (Id; refl; _∙_; inv; ap)
open import elementary-number-theory.inequality-natural-numbers using (le-ℕ)
open import
  elementary-number-theory.modular-arithmetic-standard-finite-types using
  ( mod-succ-ℕ; cong-nat-mod-succ-ℕ; leq-nat-mod-succ-ℕ)
open import elementary-number-theory.multiplication-natural-numbers using
  ( mul-ℕ; right-zero-law-mul-ℕ)
open import elementary-number-theory.natural-numbers using
  ( ℕ; zero-ℕ; succ-ℕ; is-nonzero-ℕ)
open import elementary-number-theory.standard-finite-types using
  ( nat-Fin; strict-upper-bound-nat-Fin)
```

# Euclidean division of the natural numbers

```agda
euclidean-division-ℕ :
  (k x : ℕ) → Σ ℕ (λ r → (cong-ℕ k x r) × (is-nonzero-ℕ k → le-ℕ r k))
pr1 (euclidean-division-ℕ zero-ℕ x) = x
pr1 (pr2 (euclidean-division-ℕ zero-ℕ x)) = refl-cong-ℕ zero-ℕ x
pr2 (pr2 (euclidean-division-ℕ zero-ℕ x)) f = ex-falso (f refl)
pr1 (euclidean-division-ℕ (succ-ℕ k) x) = nat-Fin (mod-succ-ℕ k x)
pr1 (pr2 (euclidean-division-ℕ (succ-ℕ k) x)) =
  symm-cong-ℕ
    ( succ-ℕ k)
    ( nat-Fin (mod-succ-ℕ k x))
    ( x)
    ( cong-nat-mod-succ-ℕ k x)
pr2 (pr2 (euclidean-division-ℕ (succ-ℕ k) x)) f =
  strict-upper-bound-nat-Fin (mod-succ-ℕ k x)

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
  Id ( mul-ℕ (quotient-euclidean-division-ℕ k x) k)
     ( dist-ℕ x (remainder-euclidean-division-ℕ k x))
eq-quotient-euclidean-division-ℕ k x =
  pr2 (cong-euclidean-division-ℕ k x)

eq-euclidean-division-ℕ :
  (k x : ℕ) →
  Id ( add-ℕ ( mul-ℕ (quotient-euclidean-division-ℕ k x) k)
             ( remainder-euclidean-division-ℕ k x))
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
