---
title: Addition on the rationals
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module elementary-number-theory.addition-rationals where

open import elementary-number-theory.addition-integers using
  ( add-ℤ; left-unit-law-add-ℤ; right-unit-law-add-ℤ)
open import elementary-number-theory.fractions using ( fraction-ℤ)
open import elementary-number-theory.multiplication-integers using
  ( mul-ℤ; is-positive-mul-ℤ; left-zero-law-mul-ℤ; associative-mul-ℤ; commutative-mul-ℤ)
open import elementary-number-theory.integers using
  ( ℤ; zero-ℤ; one-ℤ; is-positive-one-ℤ; one-positive-ℤ)
open import elementary-number-theory.rational-numbers using
  ( ℚ; zero-ℚ; in-fraction-ℤ; reduce-fraction-ℤ; is-prop-is-reduced-fraction-ℤ; eq-ℚ-sim-fractions-ℤ; unique-reduce-fraction-ℤ; in-fraction-ℤ-inv)

open import foundation.cartesian-product-types using (pair')
open import foundation.dependent-pair-types using (pair; _,_; pr1; pr2)
open import foundation.equality-cartesian-product-types using (eq-pair')
open import foundation.equality-dependent-pair-types using (eq-pair-Σ)
open import foundation.equational-reasoning
open import foundation.identity-types using
  (_＝_; refl; _∙_; inv; ap; ap-binary)
open import foundation.propositions using (eq-is-prop)

open import structured-types.pointed-types-equipped-with-automorphisms
```

## Idea

We introduce addition on the rationals and derive its basic properties. Properties of addition with respect to inequality are derived in `inequality-ratonals`.

## Definition

```agda
pre-add-ℚ : ℚ → ℚ → fraction-ℤ
pre-add-ℚ (pair (pair m (pair n (n-pos))) p) (pair (pair m' (pair n' (n'-pos))) p') = 
  pair (add-ℤ (mul-ℤ m n') (mul-ℤ m' n))
    ( pair (mul-ℤ n n') (is-positive-mul-ℤ n-pos n'-pos))

add-ℚ : ℚ → ℚ → ℚ
add-ℚ q q' = in-fraction-ℤ (pre-add-ℚ q q')
--    ( pair (add-ℤ (mul-ℤ m n') (mul-ℤ m' n))
--    ( pair (mul-ℤ n n') (is-positive-mul-ℤ n-pos n'-pos)))

add-ℚ' : ℚ → ℚ → ℚ
add-ℚ' x y = add-ℚ y x

infix 30 _+ℚ_
_+ℚ_ = add-ℚ

ap-add-ℚ :
  {x y x' y' : ℚ} → x ＝ x' → y ＝ y' → add-ℚ x y ＝ add-ℚ x' y'
ap-add-ℚ p q = ap-binary add-ℚ p q
```

## Properties

### Unit laws

```agda
abstract
  left-unit-law-add-ℚ : (k : ℚ) → zero-ℚ +ℚ k ＝ k
  left-unit-law-add-ℚ ((k1 , k2 , kpos) , kred) = 
    eq-ℚ-sim-fractions-ℤ 
      (pre-add-ℚ zero-ℚ ((k1 , k2 , kpos) , kred))
      (k1 , k2 , kpos) 
      (equational-reasoning
        mul-ℤ (add-ℤ (mul-ℤ zero-ℤ k2) (mul-ℤ k1 one-ℤ)) k2
        ＝ mul-ℤ (add-ℤ zero-ℤ (mul-ℤ k1 one-ℤ)) k2
        by ap (λ H → mul-ℤ (add-ℤ H (mul-ℤ k1 one-ℤ)) k2) 
          (left-zero-law-mul-ℤ k2)
        ＝ mul-ℤ (mul-ℤ k1 one-ℤ) k2
        by ap (λ H → mul-ℤ H k2) (left-unit-law-add-ℤ (mul-ℤ k1 one-ℤ))
        ＝ mul-ℤ k1 (mul-ℤ one-ℤ k2)
        by associative-mul-ℤ k1 one-ℤ k2)
    ∙ in-fraction-ℤ-inv ((k1 , k2 , kpos) , kred)

  right-unit-law-add-ℚ : (k : ℚ) → k +ℚ zero-ℚ ＝ k
  right-unit-law-add-ℚ ((k1 , k2 , kpos) , kred) = 
    eq-ℚ-sim-fractions-ℤ
      (pre-add-ℚ ((k1 , k2 , kpos) , kred) zero-ℚ)
      (k1 , k2 , kpos)
      (equational-reasoning
        mul-ℤ (add-ℤ (mul-ℤ k1 one-ℤ) (mul-ℤ zero-ℤ k2)) k2
        ＝ mul-ℤ (add-ℤ (mul-ℤ k1 one-ℤ) zero-ℤ) k2
        by ap (λ H → mul-ℤ (add-ℤ (mul-ℤ k1 one-ℤ) H) k2)
          (left-zero-law-mul-ℤ k2)
        ＝ mul-ℤ (mul-ℤ k1 one-ℤ) k2 
        by ap (λ H → mul-ℤ H k2) (right-unit-law-add-ℤ (mul-ℤ k1 one-ℤ))
        ＝ mul-ℤ k1 (mul-ℤ one-ℤ k2) 
        by associative-mul-ℤ k1 one-ℤ k2
        ＝ mul-ℤ k1 (mul-ℤ k2 one-ℤ)
        by ap (λ H → mul-ℤ k1 H) (commutative-mul-ℤ one-ℤ k2))
    ∙ in-fraction-ℤ-inv ((k1 , k2 , kpos) , kred)


```
