---
title: The congruence relations on the natural numbers
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module elementary-number-theory.congruence-natural-numbers where

open import elementary-number-theory.addition-natural-numbers using
  ( add-ℕ; add-ℕ'; commutative-add-ℕ)
open import elementary-number-theory.distance-natural-numbers using
  ( dist-ℕ; eq-dist-ℕ; right-unit-law-dist-ℕ; dist-eq-ℕ; symmetric-dist-ℕ;
    is-total-dist-ℕ; strict-upper-bound-dist-ℕ; is-one-dist-succ-ℕ;
    left-distributive-mul-dist-ℕ; translation-invariant-dist-ℕ)
open import elementary-number-theory.divisibility-natural-numbers using
  ( div-ℕ; div-one-ℕ; concatenate-div-eq-ℕ; div-add-ℕ; div-right-summand-ℕ;
    div-left-summand-ℕ; is-zero-div-ℕ; is-zero-div-zero-ℕ; is-one-div-one-ℕ)
open import elementary-number-theory.inequality-natural-numbers using (le-ℕ)
open import elementary-number-theory.multiplication-natural-numbers using
  ( mul-ℕ; right-zero-law-mul-ℕ; left-unit-law-mul-ℕ; left-zero-law-mul-ℕ;
    associative-mul-ℕ; commutative-mul-ℕ)
open import elementary-number-theory.natural-numbers using
  ( ℕ; zero-ℕ; succ-ℕ; is-one-ℕ)

open import foundation.coproduct-types using (inl; inr)
open import foundation.dependent-pair-types using (pair; pr1; pr2)
open import foundation.identity-types using (Id; refl; _∙_; inv; ap; tr)
open import foundation.universe-levels using (UU; lzero)

open import univalent-combinatorics.standard-finite-types using
  ( Fin; zero-Fin; nat-Fin; is-injective-nat-Fin; strict-upper-bound-nat-Fin;
    is-zero-nat-zero-Fin)
```

# The congruence relations on the natural numbers

```agda
cong-ℕ :
  ℕ → ℕ → ℕ → UU lzero
cong-ℕ k x y = div-ℕ k (dist-ℕ x y)

_≡_mod_ : ℕ → ℕ → ℕ → UU lzero
x ≡ y mod k = cong-ℕ k x y

concatenate-eq-cong-eq-ℕ :
  (k : ℕ) {x1 x2 x3 x4 : ℕ} →
  Id x1 x2 → cong-ℕ k x2 x3 → Id x3 x4 → cong-ℕ k x1 x4
concatenate-eq-cong-eq-ℕ k refl H refl = H

concatenate-eq-cong-ℕ :
  (k : ℕ) {x1 x2 x3 : ℕ} →
  Id x1 x2 → cong-ℕ k x2 x3 → cong-ℕ k x1 x3
concatenate-eq-cong-ℕ k refl H = H

concatenate-cong-eq-ℕ :
  (k : ℕ) {x1 x2 x3 : ℕ} →
  cong-ℕ k x1 x2 → Id x2 x3 → cong-ℕ k x1 x3
concatenate-cong-eq-ℕ k H refl = H

is-indiscrete-cong-one-ℕ :
  (x y : ℕ) → cong-ℕ 1 x y
is-indiscrete-cong-one-ℕ x y = div-one-ℕ (dist-ℕ x y)

is-discrete-cong-zero-ℕ :
  (x y : ℕ) → cong-ℕ zero-ℕ x y → Id x y
is-discrete-cong-zero-ℕ x y (pair k p) =
  eq-dist-ℕ x y ((inv p) ∙ (right-zero-law-mul-ℕ k))

cong-zero-ℕ :
  (k : ℕ) → cong-ℕ k k zero-ℕ
pr1 (cong-zero-ℕ k) = 1
pr2 (cong-zero-ℕ k) =
  (left-unit-law-mul-ℕ k) ∙ (inv (right-unit-law-dist-ℕ k))

refl-cong-ℕ :
  (k x : ℕ) → cong-ℕ k x x
pr1 (refl-cong-ℕ k x) = zero-ℕ
pr2 (refl-cong-ℕ k x) =
  (left-zero-law-mul-ℕ (succ-ℕ k)) ∙ (inv (dist-eq-ℕ x x refl))

cong-identification-ℕ :
  (k : ℕ) {x y : ℕ} → Id x y → cong-ℕ k x y
cong-identification-ℕ k {x} refl = refl-cong-ℕ k x

symm-cong-ℕ :
  (k x y : ℕ) → cong-ℕ k x y → cong-ℕ k y x
pr1 (symm-cong-ℕ k x y (pair d p)) = d
pr2 (symm-cong-ℕ k x y (pair d p)) = p ∙ (symmetric-dist-ℕ x y)

cong-zero-ℕ' :
  (k : ℕ) → cong-ℕ k zero-ℕ k
cong-zero-ℕ' k =
  symm-cong-ℕ k k zero-ℕ (cong-zero-ℕ k)

trans-cong-ℕ :
  (k x y z : ℕ) →
  cong-ℕ k x y → cong-ℕ k y z → cong-ℕ k x z
trans-cong-ℕ k x y z d e with is-total-dist-ℕ x y z
trans-cong-ℕ k x y z d e | inl α =
  concatenate-div-eq-ℕ (div-add-ℕ k (dist-ℕ x y) (dist-ℕ y z) d e) α
trans-cong-ℕ k x y z d e | inr (inl α) =
  div-right-summand-ℕ k (dist-ℕ y z) (dist-ℕ x z) e
    ( concatenate-div-eq-ℕ d (inv α))
trans-cong-ℕ k x y z d e | inr (inr α) =
  div-left-summand-ℕ k (dist-ℕ x z) (dist-ℕ x y) d
    ( concatenate-div-eq-ℕ e (inv α))

concatenate-cong-eq-cong-ℕ :
  {k x1 x2 x3 x4 : ℕ} →
  cong-ℕ k x1 x2 → Id x2 x3 → cong-ℕ k x3 x4 → cong-ℕ k x1 x4
concatenate-cong-eq-cong-ℕ {k} {x} {y} {.y} {z} H refl K =
  trans-cong-ℕ k x y z H K

concatenate-eq-cong-eq-cong-eq-ℕ :
  (k : ℕ) {x1 x2 x3 x4 x5 x6 : ℕ} →
  Id x1 x2 → cong-ℕ k x2 x3 → Id x3 x4 →
  cong-ℕ k x4 x5 → Id x5 x6 → cong-ℕ k x1 x6
concatenate-eq-cong-eq-cong-eq-ℕ k
  {x} {.x} {y} {.y} {z} {.z} refl H refl K refl =
  trans-cong-ℕ k x y z H K
```

```agda
eq-cong-le-dist-ℕ :
  (k x y : ℕ) → le-ℕ (dist-ℕ x y) k → cong-ℕ k x y → Id x y
eq-cong-le-dist-ℕ k x y H K =
  eq-dist-ℕ x y (is-zero-div-ℕ k (dist-ℕ x y) H K)
```

```
eq-cong-le-ℕ :
  (k x y : ℕ) → le-ℕ x k → le-ℕ y k → cong-ℕ k x y → Id x y
eq-cong-le-ℕ k x y H K =
  eq-cong-le-dist-ℕ k x y (strict-upper-bound-dist-ℕ k x y H K)
```

```agda
eq-cong-nat-Fin :
  (k : ℕ) (x y : Fin k) → cong-ℕ k (nat-Fin x) (nat-Fin y) → Id x y
eq-cong-nat-Fin (succ-ℕ k) x y H =
  is-injective-nat-Fin
    ( eq-cong-le-ℕ (succ-ℕ k) (nat-Fin x) (nat-Fin y)
      ( strict-upper-bound-nat-Fin x)
      ( strict-upper-bound-nat-Fin y)
      ( H))
```

```agda
cong-is-zero-nat-zero-Fin :
  {k : ℕ} → cong-ℕ (succ-ℕ k) (nat-Fin (zero-Fin {k})) zero-ℕ
cong-is-zero-nat-zero-Fin {k} =
  cong-identification-ℕ (succ-ℕ k) (is-zero-nat-zero-Fin {k})
```

```agda
eq-cong-zero-ℕ : (x y : ℕ) → cong-ℕ zero-ℕ x y → Id x y
eq-cong-zero-ℕ x y H =
  eq-dist-ℕ x y (is-zero-div-zero-ℕ (dist-ℕ x y) H)

is-one-cong-succ-ℕ : {k : ℕ} (x : ℕ) → cong-ℕ k x (succ-ℕ x) → is-one-ℕ k
is-one-cong-succ-ℕ {k} x H =
  is-one-div-one-ℕ k (tr (div-ℕ k) (is-one-dist-succ-ℕ x) H)
```

```agda
-- We show that congruence is invariant under scalar multiplication --

scalar-invariant-cong-ℕ :
  (k x y z : ℕ) → cong-ℕ k x y →  cong-ℕ k (mul-ℕ z x) (mul-ℕ z y)
pr1 (scalar-invariant-cong-ℕ k x y z (pair d p)) = mul-ℕ z d
pr2 (scalar-invariant-cong-ℕ k x y z (pair d p)) =
  ( associative-mul-ℕ z d k) ∙
    ( ( ap (mul-ℕ z) p) ∙
      ( left-distributive-mul-dist-ℕ x y z))

scalar-invariant-cong-ℕ' :
  (k x y z : ℕ) → cong-ℕ k x y → cong-ℕ k (mul-ℕ x z) (mul-ℕ y z)
scalar-invariant-cong-ℕ' k x y z H =
  concatenate-eq-cong-eq-ℕ k
    ( commutative-mul-ℕ x z)
    ( scalar-invariant-cong-ℕ k x y z H)
    ( commutative-mul-ℕ z y)

-- We show that multiplication respects the congruence relation --

congruence-mul-ℕ :
  (k : ℕ) {x y x' y' : ℕ} →
  cong-ℕ  k x x' → cong-ℕ k y y' → cong-ℕ k (mul-ℕ x y) (mul-ℕ x' y')
congruence-mul-ℕ k {x} {y} {x'} {y'} H K =
  trans-cong-ℕ k (mul-ℕ x y) (mul-ℕ x y') (mul-ℕ x' y')
    ( scalar-invariant-cong-ℕ k y y' x K)
    ( scalar-invariant-cong-ℕ' k x x' y' H)
```

## The congruence is translation invariant

```agda
translation-invariant-cong-ℕ :
  (k x y z : ℕ) → cong-ℕ k x y → cong-ℕ k (add-ℕ z x) (add-ℕ z y)
pr1 (translation-invariant-cong-ℕ k x y z (pair d p)) = d
pr2 (translation-invariant-cong-ℕ k x y z (pair d p)) =
  p ∙ inv (translation-invariant-dist-ℕ z x y)

translation-invariant-cong-ℕ' :
  (k x y z : ℕ) → cong-ℕ k x y → cong-ℕ k (add-ℕ x z) (add-ℕ y z)
translation-invariant-cong-ℕ' k x y z H =
  concatenate-eq-cong-eq-ℕ k
    ( commutative-add-ℕ x z)
    ( translation-invariant-cong-ℕ k x y z H)
    ( commutative-add-ℕ z y)

step-invariant-cong-ℕ :
  (k x y : ℕ) → cong-ℕ k x y → cong-ℕ k (succ-ℕ x) (succ-ℕ y)
step-invariant-cong-ℕ k x y = translation-invariant-cong-ℕ' k x y 1

reflects-cong-add-ℕ :
  {k : ℕ} (x : ℕ) {y z : ℕ} → cong-ℕ k (add-ℕ x y) (add-ℕ x z) → cong-ℕ k y z
pr1 (reflects-cong-add-ℕ {k} x {y} {z} (pair d p)) = d
pr2 (reflects-cong-add-ℕ {k} x {y} {z} (pair d p)) =
  p ∙ translation-invariant-dist-ℕ x y z

reflects-cong-add-ℕ' :
  {k : ℕ} (x : ℕ) {y z : ℕ} → cong-ℕ k (add-ℕ' x y) (add-ℕ' x z) → cong-ℕ k y z
reflects-cong-add-ℕ' {k} x {y} {z} H =
  reflects-cong-add-ℕ x {y} {z}
    ( concatenate-eq-cong-eq-ℕ k
      ( commutative-add-ℕ x y)
      ( H)
      ( commutative-add-ℕ z x))
```
