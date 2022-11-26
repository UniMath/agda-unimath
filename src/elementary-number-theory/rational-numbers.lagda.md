---
title: The rational numbers
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module elementary-number-theory.rational-numbers where

open import elementary-number-theory.absolute-value-integers using
  ( abs-ℤ; abs-neg-ℤ)
open import elementary-number-theory.bezouts-lemma using
  ( div-right-factor-coprime-ℤ)
open import elementary-number-theory.divisibility-integers using
  ( div-ℤ; antisymmetric-div-ℤ; is-plus-or-minus-sim-unit-ℤ;
    div-div-quotient-div-ℤ; sim-unit-ℤ; is-zero-sim-unit-ℤ; 
    eq-sim-unit-is-nonnegative-ℤ)
open import elementary-number-theory.equality-integers using
  ( is-decidable-is-one-ℤ; is-decidable-is-zero-ℤ; Eq-eq-ℤ)
open import elementary-number-theory.fractions using
  ( fraction-ℤ; numerator-fraction-ℤ; denominator-fraction-ℤ;
    is-positive-denominator-fraction-ℤ; is-set-fraction-ℤ; sim-fraction-ℤ;
    symm-sim-fraction-ℤ; trans-sim-fraction-ℤ)
open import elementary-number-theory.greatest-common-divisor-integers using
  ( gcd-ℤ; is-common-divisor-gcd-ℤ; is-positive-gcd-is-positive-right-ℤ;
    is-zero-right-is-zero-gcd-ℤ; is-positive-gcd-ℤ; div-gcd-is-common-divisor-ℤ;
    is-one-gcd-one-ℤ'; is-commutative-gcd-ℤ)
open import elementary-number-theory.greatest-common-divisor-natural-numbers using 
  ( gcd-ℕ)
open import elementary-number-theory.integers using
  ( ℤ; is-positive-ℤ; is-positive-eq-ℤ; zero-ℤ; one-ℤ; neg-one-ℤ; neg-ℤ;
    is-positive-int-positive-ℤ; is-zero-ℤ; neg-neg-ℤ; one-positive-ℤ; is-set-ℤ;
    is-set-positive-ℤ; is-nonnegative-is-positive-ℤ; is-prop-is-positive-ℤ; int-ℕ)
open import elementary-number-theory.multiplication-integers using
  ( mul-ℤ; is-positive-left-factor-mul-ℤ; is-injective-mul-ℤ'; associative-mul-ℤ;
    commutative-mul-ℤ; is-injective-mul-ℤ; is-plus-or-minus-ℤ; right-unit-law-mul-ℤ)
open import elementary-number-theory.natural-numbers using (ℕ)
open import elementary-number-theory.relatively-prime-integers using
  ( is-relative-prime-ℤ; is-prop-is-relative-prime-ℤ)

open import foundation.coproduct-types using (_+_; ind-coprod; inl; inr)
open import foundation.dependent-pair-types using (Σ; pair; _,_; pr1; pr2)
open import foundation.empty-types using (ex-falso)
open import foundation.equality-dependent-pair-types using (eq-pair-Σ')
open import foundation.equality-cartesian-product-types using (eq-pair')
open import foundation.equational-reasoning
open import foundation.functions using (id)
open import foundation.identity-types using (_＝_; inv; tr; refl; ap; _∙_)
open import foundation.negation using (¬)
open import foundation.propositions using (is-prop; eq-is-prop)
open import foundation.sets using
  ( Set; is-set; is-set-Σ; is-set-is-prop)
open import foundation.unit-type using (star)
open import foundation.universe-levels using (UU; lzero)
```

## Idea

The type of rational numbers is the quotient of the type of fractions, by the equivalence relation given by `(n/m) ~ (n'/m') := Id (mul-ℤ n m') (mul-ℤ n' m)`.

## Definitions

### Reduced Fraction

```agda
is-reduced-fraction-ℤ : fraction-ℤ → UU lzero
is-reduced-fraction-ℤ x =
  is-relative-prime-ℤ (numerator-fraction-ℤ x) (denominator-fraction-ℤ x)
```

### The type of rationals

```agda
ℚ : UU lzero
ℚ = Σ fraction-ℤ is-reduced-fraction-ℤ

fraction-ℚ : ℚ → fraction-ℤ
fraction-ℚ x = pr1 x

is-reduced-fraction-ℚ : (x : ℚ) → is-reduced-fraction-ℤ (fraction-ℚ x)
is-reduced-fraction-ℚ x = pr2 x
```

### Inclusion of the integers

```agda
in-int : ℤ → ℚ
in-int x = pair (pair x one-positive-ℤ) (is-one-gcd-one-ℤ' x)
```

### Negative one, zero and one

```agda
neg-one-ℚ : ℚ
neg-one-ℚ = in-int neg-one-ℤ

is-neg-one-ℚ : ℚ → UU lzero
is-neg-one-ℚ x = (x ＝ neg-one-ℚ)

zero-ℚ : ℚ
zero-ℚ = in-int zero-ℤ

is-zero-ℚ : ℚ → UU lzero
is-zero-ℚ x = (x ＝ zero-ℚ)

is-nonzero-ℚ : ℚ → UU lzero
is-nonzero-ℚ k = ¬ (is-zero-ℚ k)

one-ℚ : ℚ
one-ℚ = in-int one-ℤ

is-one-ℚ : ℚ → UU lzero
is-one-ℚ x = (x ＝ one-ℚ)
```

## Properties and constructions

```agda
is-prop-is-reduced-fraction-ℤ : (x : fraction-ℤ) → is-prop (is-reduced-fraction-ℤ x)
is-prop-is-reduced-fraction-ℤ x =
  is-prop-is-relative-prime-ℤ
    ( numerator-fraction-ℤ x)
    ( denominator-fraction-ℤ x)

reduce-numerator-fraction-ℤ :
  (x : fraction-ℤ) →
  div-ℤ
    ( gcd-ℤ (numerator-fraction-ℤ x) (denominator-fraction-ℤ x))
    ( numerator-fraction-ℤ x)
reduce-numerator-fraction-ℤ x =
  pr1 (is-common-divisor-gcd-ℤ (numerator-fraction-ℤ x) (denominator-fraction-ℤ x))

int-reduce-numerator-fraction-ℤ : fraction-ℤ → ℤ
int-reduce-numerator-fraction-ℤ x = pr1 (reduce-numerator-fraction-ℤ x)

eq-reduce-numerator-fraction-ℤ :
  (x : fraction-ℤ) →
  ( mul-ℤ
    ( int-reduce-numerator-fraction-ℤ x)
    ( gcd-ℤ (numerator-fraction-ℤ x) (denominator-fraction-ℤ x))) ＝
  ( numerator-fraction-ℤ x)
eq-reduce-numerator-fraction-ℤ x = pr2 (reduce-numerator-fraction-ℤ x)

reduce-denominator-fraction-ℤ :
  (x : fraction-ℤ) →
  div-ℤ
    ( gcd-ℤ (numerator-fraction-ℤ x) (denominator-fraction-ℤ x))
    ( denominator-fraction-ℤ x)
reduce-denominator-fraction-ℤ x =
  pr2 (is-common-divisor-gcd-ℤ (numerator-fraction-ℤ x) (denominator-fraction-ℤ x))

int-reduce-denominator-fraction-ℤ : fraction-ℤ → ℤ
int-reduce-denominator-fraction-ℤ x =
  pr1 (reduce-denominator-fraction-ℤ x)

eq-reduce-denominator-fraction-ℤ :
  (x : fraction-ℤ) →
  ( mul-ℤ
    ( int-reduce-denominator-fraction-ℤ x)
    ( gcd-ℤ (numerator-fraction-ℤ x) (denominator-fraction-ℤ x))) ＝
  ( denominator-fraction-ℤ x)
eq-reduce-denominator-fraction-ℤ x =
  pr2 (reduce-denominator-fraction-ℤ x)

is-positive-int-reduce-denominator-fraction-ℤ :
  (x : fraction-ℤ) → is-positive-ℤ (int-reduce-denominator-fraction-ℤ x)
is-positive-int-reduce-denominator-fraction-ℤ x =
  is-positive-left-factor-mul-ℤ
    ( is-positive-eq-ℤ
      ( inv (eq-reduce-denominator-fraction-ℤ x))
      ( is-positive-denominator-fraction-ℤ x))
    ( is-positive-gcd-is-positive-right-ℤ
      ( numerator-fraction-ℤ x)
      ( denominator-fraction-ℤ x)
      ( is-positive-denominator-fraction-ℤ x))

reduce-fraction-ℤ : fraction-ℤ → fraction-ℤ
reduce-fraction-ℤ x =
  pair
    ( int-reduce-numerator-fraction-ℤ x)
    ( pair
      ( int-reduce-denominator-fraction-ℤ x)
      ( is-positive-int-reduce-denominator-fraction-ℤ x))

is-reduced-reduce-fraction-ℤ :
  (x : fraction-ℤ) → is-reduced-fraction-ℤ (reduce-fraction-ℤ x)
is-reduced-reduce-fraction-ℤ x = 
   is-zero-gcd-case-split
     (is-decidable-is-zero-ℤ
       (gcd-ℤ ( numerator-fraction-ℤ (reduce-fraction-ℤ x))
         (denominator-fraction-ℤ (reduce-fraction-ℤ x))))
  where
  is-zero-gcd-case-split :
    (is-zero-ℤ (gcd-ℤ ( numerator-fraction-ℤ (reduce-fraction-ℤ x))
        (denominator-fraction-ℤ (reduce-fraction-ℤ x)))
    + ¬ (is-zero-ℤ (gcd-ℤ ( numerator-fraction-ℤ (reduce-fraction-ℤ x))
        (denominator-fraction-ℤ (reduce-fraction-ℤ x)))))
    → is-reduced-fraction-ℤ (reduce-fraction-ℤ x)
  is-zero-gcd-case-split (inl z) = 
    ex-falso (tr is-positive-ℤ
      ( is-zero-right-is-zero-gcd-ℤ 
        ( numerator-fraction-ℤ (reduce-fraction-ℤ x))  
          ( denominator-fraction-ℤ (reduce-fraction-ℤ x)) z)
          ( is-positive-denominator-fraction-ℤ (reduce-fraction-ℤ x)))
  is-zero-gcd-case-split (inr nz) = 
    is-plus-or-minus-case-split
      ( is-plus-or-minus-sim-unit-ℤ
      ( antisymmetric-div-ℤ (mul-ℤ alpha d) d
        ( div-gcd-is-common-divisor-ℤ
          ( numerator-fraction-ℤ x) ( denominator-fraction-ℤ x)
            (mul-ℤ alpha d)
          ( pair
            -- alpha * d divides the numerator of x
            ( tr ( λ - → div-ℤ - (numerator-fraction-ℤ x))
              ( commutative-mul-ℤ d alpha)
              ( div-div-quotient-div-ℤ alpha (numerator-fraction-ℤ x) d
                ( pr1 ( is-common-divisor-gcd-ℤ
                  ( numerator-fraction-ℤ x)
                  ( denominator-fraction-ℤ x)))
                ( pr1 ( is-common-divisor-gcd-ℤ
                  ( numerator-fraction-ℤ (reduce-fraction-ℤ x))
                  ( denominator-fraction-ℤ (reduce-fraction-ℤ x))))))
            -- alpha * d divides the denominator of x
            ( tr ( λ - → div-ℤ - (denominator-fraction-ℤ x))
              ( commutative-mul-ℤ d alpha)
              ( div-div-quotient-div-ℤ alpha (denominator-fraction-ℤ x) d
                ( pr2 ( is-common-divisor-gcd-ℤ
                  ( numerator-fraction-ℤ x)
                  ( denominator-fraction-ℤ x)))
                ( pr2 ( is-common-divisor-gcd-ℤ
                  ( numerator-fraction-ℤ (reduce-fraction-ℤ x))
                  ( denominator-fraction-ℤ (reduce-fraction-ℤ x))))))))
        (pair ( gcd-ℤ ( numerator-fraction-ℤ (reduce-fraction-ℤ x)) 
          ( denominator-fraction-ℤ (reduce-fraction-ℤ x))) refl)))
    where 
    alpha : ℤ 
    alpha = gcd-ℤ (numerator-fraction-ℤ (reduce-fraction-ℤ x)) 
      (denominator-fraction-ℤ (reduce-fraction-ℤ x))
    d : ℤ 
    d = gcd-ℤ (numerator-fraction-ℤ x) (denominator-fraction-ℤ x) 
    is-plus-or-minus-case-split : 
      (is-plus-or-minus-ℤ (mul-ℤ alpha d) d) 
      → is-reduced-fraction-ℤ (reduce-fraction-ℤ x)
    is-plus-or-minus-case-split (inl pos) = 
      ( is-injective-mul-ℤ' d
        ( λ r → tr is-positive-ℤ r
          ( is-positive-gcd-is-positive-right-ℤ
            ( numerator-fraction-ℤ x) ( denominator-fraction-ℤ x)
            ( is-positive-denominator-fraction-ℤ x)))) pos 
    is-plus-or-minus-case-split (inr neg) = 
      (ex-falso
        ( tr is-positive-ℤ {y = neg-ℤ one-ℤ}
          (inv (neg-neg-ℤ ( gcd-ℤ ( numerator-fraction-ℤ (reduce-fraction-ℤ x)) 
            ( denominator-fraction-ℤ (reduce-fraction-ℤ x)))) ∙
             ap neg-ℤ
               ( is-injective-mul-ℤ' d
                 ( λ r →
                   tr is-positive-ℤ r
                     ( is-positive-gcd-is-positive-right-ℤ
                       ( numerator-fraction-ℤ x)
                       ( denominator-fraction-ℤ x)
                       ( is-positive-denominator-fraction-ℤ x)))
                 ( associative-mul-ℤ neg-one-ℤ ( gcd-ℤ ( numerator-fraction-ℤ (reduce-fraction-ℤ x)) 
              ( denominator-fraction-ℤ (reduce-fraction-ℤ x)))
              d ∙ neg)))
          ( is-positive-gcd-ℤ
            ( numerator-fraction-ℤ (reduce-fraction-ℤ x))
            ( denominator-fraction-ℤ (reduce-fraction-ℤ x))
            ( inr ( is-positive-denominator-fraction-ℤ (reduce-fraction-ℤ x))))))


sim-reduced-fraction-ℤ : (x : fraction-ℤ) → (sim-fraction-ℤ x (reduce-fraction-ℤ x))
sim-reduced-fraction-ℤ x = equational-reasoning
  mul-ℤ (numerator-fraction-ℤ x) (denominator-fraction-ℤ (reduce-fraction-ℤ x))
  ＝ mul-ℤ (mul-ℤ (numerator-fraction-ℤ (reduce-fraction-ℤ x))
      (gcd-ℤ (numerator-fraction-ℤ x) (denominator-fraction-ℤ x)))
      (denominator-fraction-ℤ (reduce-fraction-ℤ x)) 
    by ap (λ H → mul-ℤ H (denominator-fraction-ℤ (reduce-fraction-ℤ x)))
        (inv (eq-reduce-numerator-fraction-ℤ x))
  ＝ mul-ℤ (numerator-fraction-ℤ (reduce-fraction-ℤ x))
    (mul-ℤ (gcd-ℤ (numerator-fraction-ℤ x) (denominator-fraction-ℤ x))
      (denominator-fraction-ℤ (reduce-fraction-ℤ x)))
    by associative-mul-ℤ (numerator-fraction-ℤ (reduce-fraction-ℤ x))
      (gcd-ℤ (numerator-fraction-ℤ x) (denominator-fraction-ℤ x))
      (denominator-fraction-ℤ (reduce-fraction-ℤ x))
  ＝ mul-ℤ (numerator-fraction-ℤ (reduce-fraction-ℤ x)) (denominator-fraction-ℤ x)
    by ap (λ H → mul-ℤ (numerator-fraction-ℤ (reduce-fraction-ℤ x)) H)
      (commutative-mul-ℤ (gcd-ℤ (numerator-fraction-ℤ x) (denominator-fraction-ℤ x)) (denominator-fraction-ℤ (reduce-fraction-ℤ x)) ∙ eq-reduce-denominator-fraction-ℤ x)

reduce-preserves-sim-ℤ : (x y : fraction-ℤ) → (H : sim-fraction-ℤ x y) →
  sim-fraction-ℤ (reduce-fraction-ℤ x) (reduce-fraction-ℤ y)
reduce-preserves-sim-ℤ x y H = 
  trans-sim-fraction-ℤ (reduce-fraction-ℤ x) y (reduce-fraction-ℤ y) 
    (trans-sim-fraction-ℤ (reduce-fraction-ℤ x) x y
      (symm-sim-fraction-ℤ x (reduce-fraction-ℤ x) (sim-reduced-fraction-ℤ x)) H)
    (sim-reduced-fraction-ℤ y)

```

### Inclusion of fractions

```agda
in-fraction-ℤ : fraction-ℤ → ℚ
in-fraction-ℤ x = pair (reduce-fraction-ℤ x) (is-reduced-reduce-fraction-ℤ x)
```

### If two fractions are related by `sim-fraction-ℤ`, then their embeddings into `ℚ` are equal
```agda
sim-unique-numerator-reduce-fraction-ℤ : (x y : fraction-ℤ) → (H : sim-fraction-ℤ x y) → sim-unit-ℤ (int-reduce-numerator-fraction-ℤ x) (int-reduce-numerator-fraction-ℤ y)
sim-unique-numerator-reduce-fraction-ℤ x y H = antisymmetric-div-ℤ
  (int-reduce-numerator-fraction-ℤ x)
  (int-reduce-numerator-fraction-ℤ y)
  div-red-x-red-y div-red-y-red-x
  where
  reduced-eqn : 
    mul-ℤ (int-reduce-numerator-fraction-ℤ x) (int-reduce-denominator-fraction-ℤ y) 
    ＝ mul-ℤ (int-reduce-numerator-fraction-ℤ y) (int-reduce-denominator-fraction-ℤ x)  
  reduced-eqn = reduce-preserves-sim-ℤ x y H
  div-red-x-num : 
    div-ℤ (int-reduce-numerator-fraction-ℤ x) (mul-ℤ (int-reduce-denominator-fraction-ℤ x) (int-reduce-numerator-fraction-ℤ y))
  div-red-x-num = pair (int-reduce-denominator-fraction-ℤ y) 
    (commutative-mul-ℤ 
      (int-reduce-denominator-fraction-ℤ y)
      (int-reduce-numerator-fraction-ℤ x) 
    ∙ (reduced-eqn 
    ∙ commutative-mul-ℤ (int-reduce-numerator-fraction-ℤ y) 
        (int-reduce-denominator-fraction-ℤ x)))
  red-x-coprime :
    gcd-ℤ (int-reduce-numerator-fraction-ℤ x) (int-reduce-denominator-fraction-ℤ x) ＝ one-ℤ
  red-x-coprime = is-reduced-reduce-fraction-ℤ x
  div-red-x-red-y : div-ℤ (int-reduce-numerator-fraction-ℤ x) (int-reduce-numerator-fraction-ℤ y)
  div-red-x-red-y = div-right-factor-coprime-ℤ 
    (int-reduce-numerator-fraction-ℤ x)
    (int-reduce-denominator-fraction-ℤ x)
    (int-reduce-numerator-fraction-ℤ y)
    div-red-x-num red-x-coprime
  div-red-y-num :
    div-ℤ (int-reduce-numerator-fraction-ℤ y) (mul-ℤ (int-reduce-denominator-fraction-ℤ y) (int-reduce-numerator-fraction-ℤ x))
  div-red-y-num = pair (int-reduce-denominator-fraction-ℤ x) 
    (commutative-mul-ℤ 
      (int-reduce-denominator-fraction-ℤ x)
      (int-reduce-numerator-fraction-ℤ y) 
    ∙ (inv (reduced-eqn) 
    ∙ commutative-mul-ℤ (int-reduce-numerator-fraction-ℤ x) 
      (int-reduce-denominator-fraction-ℤ y)))
  red-y-coprime :
    gcd-ℤ (int-reduce-numerator-fraction-ℤ y) (int-reduce-denominator-fraction-ℤ y) ＝ one-ℤ
  red-y-coprime = is-reduced-reduce-fraction-ℤ y
  div-red-y-red-x : div-ℤ (int-reduce-numerator-fraction-ℤ y) (int-reduce-numerator-fraction-ℤ x)
  div-red-y-red-x = div-right-factor-coprime-ℤ 
    (int-reduce-numerator-fraction-ℤ y)
    (int-reduce-denominator-fraction-ℤ y)
    (int-reduce-numerator-fraction-ℤ x) 
    div-red-y-num red-y-coprime 

unique-numerator-reduce-fraction-ℤ : (x y : fraction-ℤ) → (H : sim-fraction-ℤ x y) → int-reduce-numerator-fraction-ℤ x ＝ int-reduce-numerator-fraction-ℤ y
unique-numerator-reduce-fraction-ℤ x y H = 
  is-zero-num-case-split 
    (is-decidable-is-zero-ℤ (int-reduce-numerator-fraction-ℤ x))
  where
  is-zero-num-case-split : 
    (is-zero-ℤ (int-reduce-numerator-fraction-ℤ x)
    + ¬ (is-zero-ℤ (int-reduce-numerator-fraction-ℤ x)))
    → int-reduce-numerator-fraction-ℤ x ＝ int-reduce-numerator-fraction-ℤ y

  is-zero-num-case-split (inl z) =
    z ∙ inv (is-zero-sim-unit-ℤ 
      (sim-unique-numerator-reduce-fraction-ℤ x y H) z)

  is-zero-num-case-split (inr nz) = 
    is-plus-or-minus-case-split
      (is-plus-or-minus-sim-unit-ℤ (sim-unique-numerator-reduce-fraction-ℤ x y H))
    where 
    is-plus-or-minus-case-split : 
      is-plus-or-minus-ℤ (int-reduce-numerator-fraction-ℤ x) 
        (int-reduce-numerator-fraction-ℤ y)
      → int-reduce-numerator-fraction-ℤ x ＝ int-reduce-numerator-fraction-ℤ y
    is-plus-or-minus-case-split (inl pos) = pos
    is-plus-or-minus-case-split (inr neg) = ex-falso (Eq-eq-ℤ contra)
      where 
      lem : (w : ℤ) → is-positive-ℤ w → Σ ℕ (λ n → w ＝ inr (inr n))
      lem (inr (inr n)) H = pair n refl
      
      reduced-eqn : 
        mul-ℤ (int-reduce-numerator-fraction-ℤ x) (int-reduce-denominator-fraction-ℤ y) 
        ＝ mul-ℤ (int-reduce-numerator-fraction-ℤ x) (mul-ℤ neg-one-ℤ (int-reduce-denominator-fraction-ℤ x))  
      reduced-eqn = equational-reasoning
        mul-ℤ (int-reduce-numerator-fraction-ℤ x) (int-reduce-denominator-fraction-ℤ y)
        ＝ mul-ℤ (int-reduce-numerator-fraction-ℤ y) (int-reduce-denominator-fraction-ℤ x) 
        by reduce-preserves-sim-ℤ x y H
        ＝ mul-ℤ (mul-ℤ (int-reduce-numerator-fraction-ℤ x) neg-one-ℤ)
          (int-reduce-denominator-fraction-ℤ x)
        by ap (λ K → mul-ℤ K (int-reduce-denominator-fraction-ℤ x)) (inv neg ∙ commutative-mul-ℤ neg-one-ℤ (int-reduce-numerator-fraction-ℤ x)) 
        ＝ mul-ℤ (int-reduce-numerator-fraction-ℤ x) (mul-ℤ neg-one-ℤ (int-reduce-denominator-fraction-ℤ x)) 
          by associative-mul-ℤ (int-reduce-numerator-fraction-ℤ x) neg-one-ℤ (int-reduce-denominator-fraction-ℤ x)
      
      x-nat : ℕ
      x-nat = pr1 (lem (int-reduce-denominator-fraction-ℤ x) (is-positive-int-reduce-denominator-fraction-ℤ x)) 
      
      y-nat : ℕ
      y-nat = pr1 (lem (int-reduce-denominator-fraction-ℤ y) (is-positive-int-reduce-denominator-fraction-ℤ y)) 
  
      contra : inr (inr y-nat) ＝ neg-ℤ (inr (inr x-nat))
      contra = equational-reasoning
        inr (inr y-nat)
        ＝ (int-reduce-denominator-fraction-ℤ y)
        by inv (pr2 (lem (int-reduce-denominator-fraction-ℤ y) (is-positive-int-reduce-denominator-fraction-ℤ y)))
        ＝ neg-ℤ (int-reduce-denominator-fraction-ℤ x)
        by is-injective-mul-ℤ (int-reduce-numerator-fraction-ℤ x) nz reduced-eqn
        ＝ neg-ℤ (inr (inr x-nat))
        by ap neg-ℤ (pr2 (lem (int-reduce-denominator-fraction-ℤ x) (is-positive-int-reduce-denominator-fraction-ℤ x)))
 

sim-unique-denominator-reduce-fraction-ℤ : (x y : fraction-ℤ) → (H : sim-fraction-ℤ x y) → sim-unit-ℤ (int-reduce-denominator-fraction-ℤ x) (int-reduce-denominator-fraction-ℤ y)
sim-unique-denominator-reduce-fraction-ℤ x y H = antisymmetric-div-ℤ
  (int-reduce-denominator-fraction-ℤ x)
  (int-reduce-denominator-fraction-ℤ y)
  div-red-x-red-y div-red-y-red-x
  where
  reduced-eqn : 
    mul-ℤ (int-reduce-numerator-fraction-ℤ x) (int-reduce-denominator-fraction-ℤ y) 
    ＝ mul-ℤ (int-reduce-numerator-fraction-ℤ y) (int-reduce-denominator-fraction-ℤ x)  
  reduced-eqn = reduce-preserves-sim-ℤ x y H
  div-red-x-num : 
    div-ℤ (int-reduce-denominator-fraction-ℤ x) (mul-ℤ (int-reduce-numerator-fraction-ℤ x) (int-reduce-denominator-fraction-ℤ y))
  div-red-x-num = pair (int-reduce-numerator-fraction-ℤ y) 
    (inv (reduced-eqn))
  red-x-coprime :
    gcd-ℤ (int-reduce-denominator-fraction-ℤ x) (int-reduce-numerator-fraction-ℤ x) ＝ one-ℤ
  red-x-coprime = is-commutative-gcd-ℤ (int-reduce-denominator-fraction-ℤ x) (int-reduce-numerator-fraction-ℤ x) 
    ∙ is-reduced-reduce-fraction-ℤ x
  div-red-x-red-y : div-ℤ (int-reduce-denominator-fraction-ℤ x) (int-reduce-denominator-fraction-ℤ y)
  div-red-x-red-y = div-right-factor-coprime-ℤ 
    (int-reduce-denominator-fraction-ℤ x)
    (int-reduce-numerator-fraction-ℤ x)
    (int-reduce-denominator-fraction-ℤ y)
    div-red-x-num red-x-coprime
  div-red-y-num :
    div-ℤ (int-reduce-denominator-fraction-ℤ y) (mul-ℤ (int-reduce-numerator-fraction-ℤ y) (int-reduce-denominator-fraction-ℤ x))
  div-red-y-num = pair (int-reduce-numerator-fraction-ℤ x) 
    (reduced-eqn)
  red-y-coprime :
    gcd-ℤ (int-reduce-denominator-fraction-ℤ y) (int-reduce-numerator-fraction-ℤ y) ＝ one-ℤ
  red-y-coprime = is-commutative-gcd-ℤ (int-reduce-denominator-fraction-ℤ y) (int-reduce-numerator-fraction-ℤ y) 
    ∙ is-reduced-reduce-fraction-ℤ y
  div-red-y-red-x : div-ℤ (int-reduce-denominator-fraction-ℤ y) (int-reduce-denominator-fraction-ℤ x)
  div-red-y-red-x = div-right-factor-coprime-ℤ 
    (int-reduce-denominator-fraction-ℤ y)
    (int-reduce-numerator-fraction-ℤ y)
    (int-reduce-denominator-fraction-ℤ x) 
    div-red-y-num red-y-coprime 

unique-denominator-reduce-fraction-ℤ : (x y : fraction-ℤ) → (H : sim-fraction-ℤ x y) → int-reduce-denominator-fraction-ℤ x ＝ int-reduce-denominator-fraction-ℤ y
unique-denominator-reduce-fraction-ℤ x y H = 
  eq-sim-unit-is-nonnegative-ℤ 
    (is-nonnegative-is-positive-ℤ (is-positive-int-reduce-denominator-fraction-ℤ x))
    (is-nonnegative-is-positive-ℤ (is-positive-int-reduce-denominator-fraction-ℤ y))
    (sim-unique-denominator-reduce-fraction-ℤ x y H)

unique-reduce-fraction-ℤ : (x y : fraction-ℤ) → (H : sim-fraction-ℤ x y) → reduce-fraction-ℤ x ＝ reduce-fraction-ℤ y
unique-reduce-fraction-ℤ x y H =
  eq-pair' (pair
    (unique-numerator-reduce-fraction-ℤ x y H)
    (eq-pair-Σ' (pair
      (unique-denominator-reduce-fraction-ℤ x y H)
      (eq-is-prop (is-prop-is-positive-ℤ (int-reduce-denominator-fraction-ℤ y))))))

eq-ℚ-sim-fractions-ℤ : (x y : fraction-ℤ) → (H : sim-fraction-ℤ x y) → in-fraction-ℤ x ＝ in-fraction-ℤ y
eq-ℚ-sim-fractions-ℤ x y H =
  eq-pair-Σ'
    ( pair
      ( unique-reduce-fraction-ℤ x y H)
      ( eq-is-prop (is-prop-is-reduced-fraction-ℤ (reduce-fraction-ℤ y))))

reduce-is-reduced-fraction-ℤ-id : (x : fraction-ℤ) → (H : is-reduced-fraction-ℤ x) → reduce-fraction-ℤ x ＝ x
reduce-is-reduced-fraction-ℤ-id (m , n , npos) H = 
  eq-pair' (pair 
    (equational-reasoning 
      int-reduce-numerator-fraction-ℤ (m , n , npos)
      ＝ mul-ℤ (int-reduce-numerator-fraction-ℤ (m , n , npos)) one-ℤ
      by inv (right-unit-law-mul-ℤ 
        (int-reduce-numerator-fraction-ℤ (m , n , npos)))
      ＝ mul-ℤ (int-reduce-numerator-fraction-ℤ (m , n , npos)) (gcd-ℤ m n)
      by ap (λ p → mul-ℤ (int-reduce-numerator-fraction-ℤ (m , n , npos)) p)
        (inv H)
      ＝ m by eq-reduce-numerator-fraction-ℤ (m , n , npos)) 
    (eq-pair-Σ' (pair 
      (equational-reasoning 
        int-reduce-denominator-fraction-ℤ (m , n , npos)
        ＝ mul-ℤ (int-reduce-denominator-fraction-ℤ (m , n , npos)) one-ℤ
        by inv (right-unit-law-mul-ℤ 
          (int-reduce-denominator-fraction-ℤ (m , n , npos)))
        ＝ mul-ℤ (int-reduce-denominator-fraction-ℤ (m , n , npos)) (gcd-ℤ m n)
        by ap (λ p → mul-ℤ (int-reduce-denominator-fraction-ℤ (m , n , npos)) p)
          (inv H)
        ＝ n by eq-reduce-denominator-fraction-ℤ (m , n , npos)) 
      (eq-is-prop (is-prop-is-positive-ℤ n)))))


in-fraction-ℤ-inv : (q : ℚ) → in-fraction-ℤ (pr1 q) ＝ q
in-fraction-ℤ-inv (frac , red) = eq-pair-Σ' 
  (pair (reduce-is-reduced-fraction-ℤ-id frac red) 
    (eq-is-prop (is-prop-is-reduced-fraction-ℤ frac))) 
```

### The type of rationals is a set

```agda
is-set-ℚ : is-set ℚ
is-set-ℚ =
  is-set-Σ
    ( is-set-fraction-ℤ)
    ( λ x → is-set-is-prop (is-prop-is-reduced-fraction-ℤ x))

ℚ-Set : Set lzero
pr1 ℚ-Set = ℚ
pr2 ℚ-Set = is-set-ℚ

```

### Negation of rationals 

```agda
neg-ℚ : ℚ → ℚ
neg-ℚ ((n , d , pos) , red) = ((neg-ℤ n , d , pos) , 
  ap (λ H → int-ℕ (gcd-ℕ H (abs-ℤ d))) (abs-neg-ℤ n) ∙ red)
```

### Negation is an involution

```agda
neg-neg-ℚ : (k : ℚ) → neg-ℚ (neg-ℚ k) ＝ k
neg-neg-ℚ ((n , d , pos) , red) = 
  eq-pair-Σ' 
    (eq-pair' (pair (neg-neg-ℤ n) refl) , 
    (eq-is-prop (is-prop-is-reduced-fraction-ℤ (n , d , pos))))

```
