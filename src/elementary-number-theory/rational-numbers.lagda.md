---
title: The rational numbers
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module elementary-number-theory.rational-numbers where

open import elementary-number-theory.divisibility-integers using (div-ℤ)
open import elementary-number-theory.fractions using
  ( fractions-ℤ; numerator-fractions-ℤ; denominator-fractions-ℤ;
    is-positive-denominator-fractions-ℤ)
open import elementary-number-theory.greatest-common-divisor-integers using
  ( gcd-ℤ; is-common-divisor-gcd-ℤ; is-positive-gcd-is-positive-right-ℤ)
open import elementary-number-theory.integers using
  ( ℤ; is-positive-ℤ; is-positive-eq-ℤ; is-nonzero-is-positive-ℤ; is-set-ℤ)
open import elementary-number-theory.multiplication-integers using
  ( mul-ℤ; mul-ℤ'; is-positive-left-factor-mul-ℤ; is-injective-mul-ℤ; associative-mul-ℤ; commutative-mul-ℤ)
open import elementary-number-theory.relatively-prime-integers using
  ( is-relative-prime-ℤ)
open import foundation.binary-relations using (Rel-Prop; is-reflexive-Rel-Prop; is-symmetric-Rel-Prop; is-transitive-Rel-Prop)
open import foundation.equivalence-relations using (is-equivalence-relation; Eq-Rel)
open import foundation-core.propositions using (is-prop)
open import foundation-core.cartesian-product-types using (pair')

open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.identity-types using (_＝_; refl; inv; ap; _∙_)
open import foundation.universe-levels using (UU; lzero)
```

## Idea

The type of rational numbers is the quotient of the type of fractions, by the equivalence relation given by `(n/m) ~ (n'/m') := Id (mul-ℤ n m') (mul-ℤ n' m)`.

```agda
is-reduced-fractions-ℤ : fractions-ℤ → UU lzero
is-reduced-fractions-ℤ x =
  is-relative-prime-ℤ (numerator-fractions-ℤ x) (denominator-fractions-ℤ x)

ℚ : UU lzero
ℚ = Σ fractions-ℤ is-reduced-fractions-ℤ

reduce-numerator-fractions-ℤ :
  (x : fractions-ℤ) →
  div-ℤ (gcd-ℤ (numerator-fractions-ℤ x) (denominator-fractions-ℤ x)) (numerator-fractions-ℤ x)
reduce-numerator-fractions-ℤ x =
  pr1 (is-common-divisor-gcd-ℤ (numerator-fractions-ℤ x) (denominator-fractions-ℤ x))

int-reduce-numerator-fractions-ℤ : fractions-ℤ → ℤ
int-reduce-numerator-fractions-ℤ x = pr1 (reduce-numerator-fractions-ℤ x)

eq-reduce-numerator-fractions-ℤ :
  (x : fractions-ℤ) →
  ( mul-ℤ
    ( int-reduce-numerator-fractions-ℤ x)
    ( gcd-ℤ (numerator-fractions-ℤ x) (denominator-fractions-ℤ x))) ＝
  ( numerator-fractions-ℤ x)
eq-reduce-numerator-fractions-ℤ x = pr2 (reduce-numerator-fractions-ℤ x)

reduce-denominator-fractions-ℤ :
  (x : fractions-ℤ) →
  div-ℤ (gcd-ℤ (numerator-fractions-ℤ x) (denominator-fractions-ℤ x)) (denominator-fractions-ℤ x)
reduce-denominator-fractions-ℤ x =
  pr2 (is-common-divisor-gcd-ℤ (numerator-fractions-ℤ x) (denominator-fractions-ℤ x))

int-reduce-denominator-fractions-ℤ : fractions-ℤ → ℤ
int-reduce-denominator-fractions-ℤ x =
  pr1 (reduce-denominator-fractions-ℤ x)

eq-reduce-denominator-fractions-ℤ :
  (x : fractions-ℤ) →
  ( mul-ℤ
    ( int-reduce-denominator-fractions-ℤ x)
    ( gcd-ℤ (numerator-fractions-ℤ x) (denominator-fractions-ℤ x))) ＝
  ( denominator-fractions-ℤ x)
eq-reduce-denominator-fractions-ℤ x =
  pr2 (reduce-denominator-fractions-ℤ x)

is-positive-int-reduce-denominator-fractions-ℤ :
  (x : fractions-ℤ) → is-positive-ℤ (int-reduce-denominator-fractions-ℤ x)
is-positive-int-reduce-denominator-fractions-ℤ x =
  is-positive-left-factor-mul-ℤ
    ( is-positive-eq-ℤ
      ( inv (eq-reduce-denominator-fractions-ℤ x))
      ( is-positive-denominator-fractions-ℤ x))
    ( is-positive-gcd-is-positive-right-ℤ
      ( numerator-fractions-ℤ x)
      ( denominator-fractions-ℤ x)
      ( is-positive-denominator-fractions-ℤ x))

reduce-fractions-ℤ : fractions-ℤ → fractions-ℤ
reduce-fractions-ℤ x =
  pair
    ( int-reduce-numerator-fractions-ℤ x)
    ( pair
      ( int-reduce-denominator-fractions-ℤ x)
      ( is-positive-int-reduce-denominator-fractions-ℤ x))

{-
is-reduced-reduce-fractions-ℤ :
  (x : fractions-ℤ) → is-reduced-fractions-ℤ (reduce-fractions-ℤ x)
is-reduced-reduce-fractions-ℤ x = {!!}
-}
 
fraction-simpl-type : fractions-ℤ → fractions-ℤ → UU lzero
fraction-simpl-type (pair a (pair b _)) (pair c (pair d _)) = 
  mul-ℤ a d ＝ mul-ℤ c b 

fraction-simpl-is-prop : (q : fractions-ℤ) (r : fractions-ℤ) 
  → is-prop (fraction-simpl-type q r)
fraction-simpl-is-prop (pair a (pair b _)) (pair c (pair d _)) =
  is-set-ℤ (mul-ℤ a d) (mul-ℤ c b) 

fraction-simpl : Rel-Prop lzero fractions-ℤ
fraction-simpl q r = pair (fraction-simpl-type q r) (fraction-simpl-is-prop q r)

fraction-simpl-refl : is-reflexive-Rel-Prop fraction-simpl
fraction-simpl-refl {x} = refl 

fraction-simpl-sym : is-symmetric-Rel-Prop fraction-simpl
fraction-simpl-sym = (λ p → inv p)

fraction-simpl-trans : is-transitive-Rel-Prop fraction-simpl
fraction-simpl-trans {x} {y} {z} p q = 
  is-injective-mul-ℤ (pr1 (pr2 y)) 
  (is-nonzero-is-positive-ℤ (pr1 (pr2 y)) (pr2 (pr2 y))) 
  ( inv (associative-mul-ℤ (pr1 (pr2 y)) (pr1 x) (pr1 (pr2 z))) 
    ∙ (ap (mul-ℤ' (pr1 (pr2 z))) p-flip 
    ∙ (associative-mul-ℤ (pr1 (pr2 x)) (pr1 y) (pr1 (pr2 z)) 
    ∙ (ap (mul-ℤ (pr1 (pr2 x))) q 
    ∙ (ap (mul-ℤ (pr1 (pr2 x))) (commutative-mul-ℤ (pr1 z) (pr1 (pr2 y)))
    ∙ (commutative-mul-ℤ (pr1 (pr2 x)) (mul-ℤ (pr1 (pr2 y)) (pr1 z)) 
    ∙ (associative-mul-ℤ (pr1 (pr2 y)) (pr1 z) (pr1 (pr2 x))))))))) 
  where
    p-flip : mul-ℤ (pr1 (pr2 y)) (pr1 x) ＝ mul-ℤ (pr1 (pr2 x)) (pr1 y)
    p-flip = commutative-mul-ℤ (pr1 (pr2 y)) (pr1 x) 
             ∙ ( p 
             ∙ ( commutative-mul-ℤ (pr1 y) (pr1 (pr2 x)) ) )

fraction-simpl-eq : is-equivalence-relation fraction-simpl
fraction-simpl-eq = pair' (λ {x} → fraction-simpl-refl {x}) 
  (pair' (λ {x} {y} p → fraction-simpl-sym {x} {y} p) 
  (λ {x} {y} {z} p q →  fraction-simpl-trans {x} {y} {z} p q))  

fraction-simpl-eq-rel : Eq-Rel lzero fractions-ℤ
fraction-simpl-eq-rel = pair fraction-simpl fraction-simpl-eq

```
