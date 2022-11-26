---
title: Addition on the rationals
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module elementary-number-theory.addition-rationals where

open import elementary-number-theory.addition-integers using
  ( add-ℤ; left-unit-law-add-ℤ; right-unit-law-add-ℤ; commutative-add-ℤ; left-inverse-law-add-ℤ; associative-add-ℤ)
open import elementary-number-theory.fractions using ( fraction-ℤ; numerator-fraction-ℤ; denominator-fraction-ℤ)
open import elementary-number-theory.greatest-common-divisor-integers using ( gcd-ℤ; is-positive-gcd-is-positive-right-ℤ)
open import elementary-number-theory.multiplication-integers using
  ( mul-ℤ; is-positive-mul-ℤ; left-zero-law-mul-ℤ; associative-mul-ℤ;
  commutative-mul-ℤ; left-negative-law-mul-ℤ; right-unit-law-mul-ℤ; 
  is-injective-mul-ℤ'; interchange-law-mul-mul-ℤ; right-distributive-mul-add-ℤ)
open import elementary-number-theory.integers using
  ( ℤ; zero-ℤ; one-ℤ; is-positive-ℤ; is-positive-one-ℤ; one-positive-ℤ; neg-ℤ; is-nonzero-ℤ; is-nonzero-is-positive-ℤ)
open import elementary-number-theory.rational-numbers using
  ( ℚ; zero-ℚ; in-fraction-ℤ; is-reduced-fraction-ℤ; reduce-fraction-ℤ;
    is-prop-is-reduced-fraction-ℤ; eq-ℚ-sim-fractions-ℤ; 
    unique-reduce-fraction-ℤ; in-fraction-ℤ-inv; neg-ℚ; 
    int-reduce-numerator-fraction-ℤ; int-reduce-denominator-fraction-ℤ;
    eq-reduce-numerator-fraction-ℤ; eq-reduce-denominator-fraction-ℤ)

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

### Associativity of addition
```agda 
abstract
  associative-add-ℚ : (k l m : ℚ) → ((k +ℚ l) +ℚ m) ＝ (k +ℚ (l +ℚ m))
  associative-add-ℚ ((k1 , k2 , kpos) , kred) ((l1 , l2 , lpos) , lred)
    ((m1 , m2 , mpos) , mred) = 
    eq-ℚ-sim-fractions-ℤ 
      (pre-add-ℚ 
        (((k1 , k2 , kpos) , kred) +ℚ ((l1 , l2 , lpos) , lred)) 
        ((m1 , m2 , mpos) , mred))
      (pre-add-ℚ  
        ((k1 , k2 , kpos) , kred) 
        (((l1 , l2 , lpos) , lred) +ℚ ((m1 , m2 , mpos) , mred))) 
      (is-injective-mul-ℤ' (mul-ℤ l-gcd r-gcd) nz-factor eqn) 
    where
    left : fraction-ℤ
    left = pre-add-ℚ ((k1 , k2 , kpos) , kred) ((l1 , l2 , lpos) , lred)
    l-gcd : ℤ
    l-gcd = gcd-ℤ (numerator-fraction-ℤ left) (denominator-fraction-ℤ left)
    l-gcd-pos : is-positive-ℤ l-gcd
    l-gcd-pos = 
      is-positive-gcd-is-positive-right-ℤ 
        (numerator-fraction-ℤ left) (denominator-fraction-ℤ left)
        (is-positive-mul-ℤ kpos lpos)
    l-num : ℤ
    l-num = int-reduce-numerator-fraction-ℤ left
    l-num-eqn : mul-ℤ l-num l-gcd ＝ add-ℤ (mul-ℤ k1 l2) (mul-ℤ l1 k2)
    l-num-eqn = eq-reduce-numerator-fraction-ℤ left
    l-denom : ℤ
    l-denom = int-reduce-denominator-fraction-ℤ left
    l-denom-eqn : mul-ℤ l-denom l-gcd ＝ mul-ℤ k2 l2
    l-denom-eqn = eq-reduce-denominator-fraction-ℤ left

    right : fraction-ℤ
    right = pre-add-ℚ ((l1 , l2 , lpos) , lred) ((m1 , m2 , mpos) , mred) 
    r-gcd : ℤ
    r-gcd = gcd-ℤ (numerator-fraction-ℤ right) (denominator-fraction-ℤ right)
    r-gcd-pos : is-positive-ℤ r-gcd
    r-gcd-pos = 
      is-positive-gcd-is-positive-right-ℤ 
        (numerator-fraction-ℤ right) (denominator-fraction-ℤ right)
        (is-positive-mul-ℤ lpos mpos)
    r-num : ℤ
    r-num = int-reduce-numerator-fraction-ℤ right
    r-num-eqn : mul-ℤ r-num r-gcd ＝ add-ℤ (mul-ℤ l1 m2) (mul-ℤ m1 l2)
    r-num-eqn = eq-reduce-numerator-fraction-ℤ right
    r-denom : ℤ
    r-denom = int-reduce-denominator-fraction-ℤ right
    r-denom-eqn : mul-ℤ r-denom r-gcd ＝ mul-ℤ l2 m2
    r-denom-eqn = eq-reduce-denominator-fraction-ℤ right

    nz-factor : is-nonzero-ℤ (mul-ℤ l-gcd r-gcd)
    nz-factor = is-nonzero-is-positive-ℤ (mul-ℤ l-gcd r-gcd) 
      (is-positive-mul-ℤ l-gcd-pos r-gcd-pos)

    eqn : mul-ℤ (mul-ℤ (add-ℤ (mul-ℤ l-num m2) (mul-ℤ m1 l-denom)) 
      (mul-ℤ k2 r-denom)) (mul-ℤ l-gcd r-gcd)
      ＝ mul-ℤ (mul-ℤ (add-ℤ (mul-ℤ k1 r-denom) (mul-ℤ r-num k2)) 
      (mul-ℤ l-denom m2)) (mul-ℤ l-gcd r-gcd)
    eqn = equational-reasoning
      mul-ℤ (mul-ℤ (add-ℤ (mul-ℤ l-num m2) (mul-ℤ m1 l-denom)) 
        (mul-ℤ k2 r-denom)) (mul-ℤ l-gcd r-gcd)
      ＝ mul-ℤ 
        (mul-ℤ (add-ℤ (mul-ℤ l-num m2) (mul-ℤ m1 l-denom)) l-gcd) 
        (mul-ℤ (mul-ℤ k2 r-denom) r-gcd) 
      by interchange-law-mul-mul-ℤ 
        (add-ℤ (mul-ℤ l-num m2) (mul-ℤ m1 l-denom))
        (mul-ℤ k2 r-denom) l-gcd r-gcd
      ＝ mul-ℤ 
        (mul-ℤ (add-ℤ (mul-ℤ l-num m2) (mul-ℤ m1 l-denom)) l-gcd) 
        (mul-ℤ (mul-ℤ l-denom m2) l-gcd)
      by ap (λ H → mul-ℤ
        (mul-ℤ (add-ℤ (mul-ℤ l-num m2) (mul-ℤ m1 l-denom)) l-gcd) H)
        (equational-reasoning
          mul-ℤ (mul-ℤ k2 r-denom) r-gcd 
          ＝ mul-ℤ k2 (mul-ℤ r-denom r-gcd) by associative-mul-ℤ k2 r-denom r-gcd
          ＝ mul-ℤ k2 (mul-ℤ l2 m2) by ap (λ K → mul-ℤ k2 K) r-denom-eqn
          ＝ mul-ℤ (mul-ℤ k2 l2) m2 by inv (associative-mul-ℤ k2 l2 m2)
          ＝ mul-ℤ (mul-ℤ l-denom l-gcd) m2 
            by ap (λ K → mul-ℤ K m2) (inv l-denom-eqn)
          ＝ mul-ℤ l-denom (mul-ℤ l-gcd m2) by associative-mul-ℤ l-denom l-gcd m2
          ＝ mul-ℤ l-denom (mul-ℤ m2 l-gcd) 
            by ap (λ K → mul-ℤ l-denom K) (commutative-mul-ℤ l-gcd m2)
          ＝ mul-ℤ (mul-ℤ l-denom m2) l-gcd 
            by inv (associative-mul-ℤ l-denom m2 l-gcd))
      ＝ mul-ℤ
        (mul-ℤ (add-ℤ (mul-ℤ k1 r-denom) (mul-ℤ r-num k2)) r-gcd)
        (mul-ℤ (mul-ℤ l-denom m2) l-gcd)
      by ap (λ H → mul-ℤ H (mul-ℤ (mul-ℤ l-denom m2) l-gcd))
        (equational-reasoning
          mul-ℤ (add-ℤ (mul-ℤ l-num m2) (mul-ℤ m1 l-denom)) l-gcd
          ＝ add-ℤ (mul-ℤ (mul-ℤ l-num m2) l-gcd)
             (mul-ℤ (mul-ℤ m1 l-denom) l-gcd)
          by right-distributive-mul-add-ℤ (mul-ℤ l-num m2)
            (mul-ℤ m1 l-denom) l-gcd
          ＝ add-ℤ (mul-ℤ (mul-ℤ l-num m2) l-gcd) 
            (mul-ℤ (mul-ℤ m1 l2) k2) 
          by ap (λ K → add-ℤ (mul-ℤ (mul-ℤ l-num m2) l-gcd) K)
            (equational-reasoning 
              mul-ℤ (mul-ℤ m1 l-denom) l-gcd
              ＝ mul-ℤ m1 (mul-ℤ l-denom l-gcd) 
              by associative-mul-ℤ m1 l-denom l-gcd
              ＝ mul-ℤ m1 (mul-ℤ l2 k2) 
              by ap (λ P → mul-ℤ m1 P) 
                (l-denom-eqn ∙ commutative-mul-ℤ k2 l2)
              ＝ mul-ℤ (mul-ℤ m1 l2) k2
              by inv (associative-mul-ℤ m1 l2 k2))
          ＝ add-ℤ (add-ℤ (mul-ℤ (mul-ℤ k1 l2) m2) (mul-ℤ (mul-ℤ l1 k2) m2)) 
            (mul-ℤ (mul-ℤ m1 l2) k2)
          by ap (λ K → add-ℤ K (mul-ℤ (mul-ℤ m1 l2) k2)) 
            (equational-reasoning 
              mul-ℤ (mul-ℤ l-num m2) l-gcd
              ＝ mul-ℤ l-gcd (mul-ℤ l-num m2)
              by commutative-mul-ℤ (mul-ℤ l-num m2) l-gcd
              ＝ mul-ℤ (mul-ℤ l-gcd l-num) m2
              by inv (associative-mul-ℤ l-gcd l-num m2)
              ＝ mul-ℤ (add-ℤ (mul-ℤ k1 l2) (mul-ℤ l1 k2)) m2
              by ap (λ P → mul-ℤ P m2) 
                (commutative-mul-ℤ l-gcd l-num ∙ l-num-eqn)
              ＝ add-ℤ (mul-ℤ (mul-ℤ k1 l2) m2) (mul-ℤ (mul-ℤ l1 k2) m2)
              by right-distributive-mul-add-ℤ (mul-ℤ k1 l2) (mul-ℤ l1 k2) m2)
          ＝ add-ℤ (mul-ℤ (mul-ℤ k1 l2) m2)
            (add-ℤ (mul-ℤ (mul-ℤ l1 k2) m2) (mul-ℤ (mul-ℤ m1 l2) k2))
          by associative-add-ℤ (mul-ℤ (mul-ℤ k1 l2) m2)
            (mul-ℤ (mul-ℤ l1 k2) m2) (mul-ℤ (mul-ℤ m1 l2) k2)
          ＝ add-ℤ (mul-ℤ (mul-ℤ k1 l2) m2) 
            (mul-ℤ (mul-ℤ r-num k2) r-gcd)
          by ap (λ H → add-ℤ (mul-ℤ (mul-ℤ k1 l2) m2) H) 
            (equational-reasoning 
            add-ℤ (mul-ℤ (mul-ℤ l1 k2) m2) (mul-ℤ (mul-ℤ m1 l2) k2)
            ＝ add-ℤ (mul-ℤ (mul-ℤ l1 m2) k2) (mul-ℤ (mul-ℤ m1 l2) k2)
            by ap (λ K → add-ℤ K (mul-ℤ (mul-ℤ m1 l2) k2))
              (equational-reasoning
                mul-ℤ (mul-ℤ l1 k2) m2 
                ＝ mul-ℤ l1 (mul-ℤ k2 m2) by associative-mul-ℤ l1 k2 m2
                ＝ mul-ℤ l1 (mul-ℤ m2 k2) 
                  by ap (λ P → mul-ℤ l1 P) (commutative-mul-ℤ k2 m2)
                ＝ mul-ℤ (mul-ℤ l1 m2) k2 by inv (associative-mul-ℤ l1 m2 k2))
            ＝ mul-ℤ (add-ℤ (mul-ℤ l1 m2) (mul-ℤ m1 l2)) k2
            by inv (right-distributive-mul-add-ℤ (mul-ℤ l1 m2) (mul-ℤ m1 l2) k2)
            ＝ mul-ℤ (mul-ℤ r-num r-gcd) k2 
            by ap (λ K → mul-ℤ K k2) (inv r-num-eqn)
            ＝ mul-ℤ r-num (mul-ℤ r-gcd k2) by associative-mul-ℤ r-num r-gcd k2 
            ＝ mul-ℤ r-num (mul-ℤ k2 r-gcd)
            by ap (λ K → mul-ℤ r-num K) (commutative-mul-ℤ r-gcd k2)
            ＝ mul-ℤ (mul-ℤ r-num k2) r-gcd  
            by inv (associative-mul-ℤ r-num k2 r-gcd))
          ＝ add-ℤ (mul-ℤ (mul-ℤ k1 r-denom) r-gcd)
             (mul-ℤ (mul-ℤ r-num k2) r-gcd)
          by ap (λ H → add-ℤ H (mul-ℤ (mul-ℤ r-num k2) r-gcd))
            (equational-reasoning 
              mul-ℤ (mul-ℤ k1 l2) m2
              ＝ mul-ℤ k1 (mul-ℤ l2 m2) by associative-mul-ℤ k1 l2 m2
              ＝ mul-ℤ k1 (mul-ℤ r-denom r-gcd)
              by ap (λ K → mul-ℤ k1 K) (inv r-denom-eqn)
              ＝ mul-ℤ (mul-ℤ k1 r-denom) r-gcd
              by inv (associative-mul-ℤ k1 r-denom r-gcd))
          ＝ mul-ℤ (add-ℤ (mul-ℤ k1 r-denom) (mul-ℤ r-num k2)) r-gcd
          by inv (right-distributive-mul-add-ℤ (mul-ℤ k1 r-denom)
            (mul-ℤ r-num k2) r-gcd)) 
      ＝ mul-ℤ (mul-ℤ (add-ℤ (mul-ℤ k1 r-denom) (mul-ℤ r-num k2)) 
        (mul-ℤ l-denom m2)) (mul-ℤ r-gcd l-gcd)
      by interchange-law-mul-mul-ℤ 
        (add-ℤ (mul-ℤ k1 r-denom) (mul-ℤ r-num k2)) r-gcd
        (mul-ℤ l-denom m2) l-gcd
      ＝ mul-ℤ (mul-ℤ (add-ℤ (mul-ℤ k1 r-denom) (mul-ℤ r-num k2)) 
        (mul-ℤ l-denom m2)) (mul-ℤ l-gcd r-gcd)
      by ap (λ H → mul-ℤ (mul-ℤ (add-ℤ (mul-ℤ k1 r-denom) (mul-ℤ r-num k2))
        (mul-ℤ l-denom m2)) H) (commutative-mul-ℤ r-gcd l-gcd)  
```

### Commutativity of addition
```agda
abstract
  commutative-add-ℚ : (k l : ℚ) → k +ℚ l ＝ l +ℚ k
  commutative-add-ℚ ((k1 , k2 , kpos) , kred) ((l1 , l2 , lpos) , lred) =
    eq-ℚ-sim-fractions-ℤ
      (pre-add-ℚ
        ((k1 , k2 , kpos) , kred) ((l1 , l2 , lpos) , lred))
      (pre-add-ℚ
        ((l1 , l2 , lpos) , lred) ((k1 , k2 , kpos) , kred))
      (equational-reasoning
        mul-ℤ (add-ℤ (mul-ℤ k1 l2) (mul-ℤ l1 k2)) (mul-ℤ l2 k2)
        ＝ mul-ℤ (add-ℤ (mul-ℤ k1 l2) (mul-ℤ l1 k2)) (mul-ℤ k2 l2)
        by ap (λ H → mul-ℤ (add-ℤ (mul-ℤ k1 l2) (mul-ℤ l1 k2)) H)
          (commutative-mul-ℤ l2 k2)
        ＝ mul-ℤ (add-ℤ (mul-ℤ l1 k2) (mul-ℤ k1 l2)) (mul-ℤ k2 l2)
        by ap (λ H → mul-ℤ H (mul-ℤ k2 l2)) 
          (commutative-add-ℤ (mul-ℤ k1 l2) (mul-ℤ l1 k2)))
```

### Inverse laws for addition
```agda
abstract
  left-inverse-law-add-ℚ : 
    (k : ℚ) → (neg-ℚ k) +ℚ k ＝ zero-ℚ
  left-inverse-law-add-ℚ ((k1 , k2 , kpos) , kred) = 
    eq-ℚ-sim-fractions-ℤ
      (pre-add-ℚ ((neg-ℤ k1 , k2 , kpos) , neg-red) ((k1 , k2 , kpos) , kred))
      (zero-ℤ , one-ℤ , is-positive-one-ℤ)
      (equational-reasoning
        mul-ℤ (add-ℤ (mul-ℤ (neg-ℤ k1) k2) (mul-ℤ k1 k2)) one-ℤ
        ＝ add-ℤ (mul-ℤ (neg-ℤ k1) k2) (mul-ℤ k1 k2)
        by right-unit-law-mul-ℤ (add-ℤ (mul-ℤ (neg-ℤ k1) k2) (mul-ℤ k1 k2)) 
        ＝ add-ℤ (neg-ℤ (mul-ℤ k1 k2)) (mul-ℤ k1 k2)
        by ap (λ H → add-ℤ H (mul-ℤ k1 k2)) (left-negative-law-mul-ℤ k1 k2)
        ＝ zero-ℤ
        by left-inverse-law-add-ℤ (mul-ℤ k1 k2)
        ＝ mul-ℤ zero-ℤ (mul-ℤ k2 k2)
        by inv (left-zero-law-mul-ℤ (mul-ℤ k2 k2)))
    ∙ in-fraction-ℤ-inv zero-ℚ
    where 
      neg-red : is-reduced-fraction-ℤ (neg-ℤ k1 , k2 , kpos) 
      neg-red = pr2 (neg-ℚ ((k1 , k2 , kpos) , kred))
  
  right-inverse-law-add-ℚ : 
    (k : ℚ) → k +ℚ (neg-ℚ k) ＝ zero-ℚ
  right-inverse-law-add-ℚ k = 
    commutative-add-ℚ k (neg-ℚ k) ∙ left-inverse-law-add-ℚ k
```


