---
title: Univalent Mathematics in Agda
---

```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module foundations.difference-integers where

open import foundations.addition-integers using
  ( add-ℤ; right-unit-law-add-ℤ; left-inverse-law-add-ℤ; associative-add-ℤ;
    add-ℤ'; left-unit-law-add-ℤ; right-inverse-law-add-ℤ;
    right-predecessor-law-add-ℤ; left-predecessor-law-add-ℤ;
    right-successor-law-add-ℤ; distributive-neg-add-ℤ; commutative-add-ℤ;
    left-successor-law-add-ℤ; interchange-law-add-add-ℤ)
open import foundations.identity-types using (Id; refl; _∙_; inv; ap; ap-binary)
open import foundations.integers using
  ( ℤ; neg-ℤ; is-zero-ℤ; zero-ℤ; succ-ℤ; pred-ℤ;
    neg-succ-ℤ; neg-pred-ℤ; neg-neg-ℤ)
open import foundations.multiplication-integers using
  ( mul-ℤ; right-negative-law-mul-ℤ; left-distributive-mul-add-ℤ;
    left-negative-law-mul-ℤ; right-distributive-mul-add-ℤ)
open import foundations.laws-for-operations using
  ( interchange-law; interchange-law-commutative-and-associative)

```

# The difference between integers

```
diff-ℤ : ℤ → ℤ → ℤ
diff-ℤ x y = add-ℤ x (neg-ℤ y)

ap-diff-ℤ : {x x' y y' : ℤ} → Id x x' → Id y y' → Id (diff-ℤ x y) (diff-ℤ x' y')
ap-diff-ℤ p q = ap-binary diff-ℤ p q

eq-diff-ℤ : {x y : ℤ} → is-zero-ℤ (diff-ℤ x y) → Id x y
eq-diff-ℤ {x} {y} H =
  ( inv (right-unit-law-add-ℤ x)) ∙
  ( ( ap (add-ℤ x) (inv (left-inverse-law-add-ℤ y))) ∙
    ( ( inv (associative-add-ℤ x (neg-ℤ y) y)) ∙
      ( ( ap (add-ℤ' y) H) ∙
        ( left-unit-law-add-ℤ y))))

is-zero-diff-ℤ' : (x : ℤ) → is-zero-ℤ (diff-ℤ x x)
is-zero-diff-ℤ' x = right-inverse-law-add-ℤ x

is-zero-diff-ℤ :
  {x y : ℤ} → Id x y → is-zero-ℤ (diff-ℤ x y)
is-zero-diff-ℤ {x} {.x} refl = is-zero-diff-ℤ' x

left-zero-law-diff-ℤ : (x : ℤ) → Id (diff-ℤ zero-ℤ x) (neg-ℤ x)
left-zero-law-diff-ℤ x = left-unit-law-add-ℤ (neg-ℤ x)

right-zero-law-diff-ℤ : (x : ℤ) → Id (diff-ℤ x zero-ℤ) x
right-zero-law-diff-ℤ x = right-unit-law-add-ℤ x

left-successor-law-diff-ℤ :
  (x y : ℤ) → Id (diff-ℤ (succ-ℤ x) y) (succ-ℤ (diff-ℤ x y))
left-successor-law-diff-ℤ x y = left-successor-law-add-ℤ x (neg-ℤ y)

right-successor-law-diff-ℤ :
  (x y : ℤ) → Id (diff-ℤ x (succ-ℤ y)) (pred-ℤ (diff-ℤ x y))
right-successor-law-diff-ℤ x y =
  ap (add-ℤ x) (neg-succ-ℤ y) ∙ right-predecessor-law-add-ℤ x (neg-ℤ y)

left-predecessor-law-diff-ℤ :
  (x y : ℤ) → Id (diff-ℤ (pred-ℤ x) y) (pred-ℤ (diff-ℤ x y))
left-predecessor-law-diff-ℤ x y = left-predecessor-law-add-ℤ x (neg-ℤ y)

right-predecessor-law-diff-ℤ :
  (x y : ℤ) → Id (diff-ℤ x (pred-ℤ y)) (succ-ℤ (diff-ℤ x y))
right-predecessor-law-diff-ℤ x y =
  ap (add-ℤ x) (neg-pred-ℤ y) ∙ right-successor-law-add-ℤ x (neg-ℤ y)

triangle-diff-ℤ :
  (x y z : ℤ) → Id (add-ℤ (diff-ℤ x y) (diff-ℤ y z)) (diff-ℤ x z)
triangle-diff-ℤ x y z =
  ( associative-add-ℤ x (neg-ℤ y) (diff-ℤ y z)) ∙
  ( ap
    ( add-ℤ x)
    ( ( inv (associative-add-ℤ (neg-ℤ y) y (neg-ℤ z))) ∙
      ( ( ap (add-ℤ' (neg-ℤ z)) (left-inverse-law-add-ℤ y)) ∙
        ( left-unit-law-add-ℤ (neg-ℤ z)))))

distributive-neg-diff-ℤ :
  (x y : ℤ) → Id (neg-ℤ (diff-ℤ x y)) (diff-ℤ y x)
distributive-neg-diff-ℤ x y =
  ( distributive-neg-add-ℤ x (neg-ℤ y)) ∙
  ( ( ap (add-ℤ (neg-ℤ x)) (neg-neg-ℤ y)) ∙
    ( commutative-add-ℤ (neg-ℤ x) y))

interchange-law-add-diff-ℤ : interchange-law add-ℤ diff-ℤ
interchange-law-add-diff-ℤ x y u v =
  ( interchange-law-add-add-ℤ x (neg-ℤ y) u (neg-ℤ v)) ∙
  ( ap (add-ℤ (add-ℤ x u)) (inv (distributive-neg-add-ℤ y v)))

interchange-law-diff-add-ℤ : interchange-law diff-ℤ add-ℤ
interchange-law-diff-add-ℤ x y u v = inv (interchange-law-add-diff-ℤ x u y v)

left-translation-diff-ℤ :
  (x y z : ℤ) → Id (diff-ℤ (add-ℤ z x) (add-ℤ z y)) (diff-ℤ x y)
left-translation-diff-ℤ x y z =
  ( interchange-law-diff-add-ℤ z x z y) ∙
  ( ( ap (add-ℤ' (diff-ℤ x y)) (right-inverse-law-add-ℤ z)) ∙
    ( left-unit-law-add-ℤ (diff-ℤ x y)))

right-translation-diff-ℤ :
  (x y z : ℤ) → Id (diff-ℤ (add-ℤ x z) (add-ℤ y z)) (diff-ℤ x y)
right-translation-diff-ℤ x y z =
  ( ap-diff-ℤ (commutative-add-ℤ x z) (commutative-add-ℤ y z)) ∙
  ( left-translation-diff-ℤ x y z)

linear-diff-ℤ :
  (z x y : ℤ) → Id (diff-ℤ (mul-ℤ z x) (mul-ℤ z y)) (mul-ℤ z (diff-ℤ x y))
linear-diff-ℤ z x y =
  ( ap (add-ℤ (mul-ℤ z x)) (inv (right-negative-law-mul-ℤ z y))) ∙
  ( inv (left-distributive-mul-add-ℤ z x (neg-ℤ y)))

linear-diff-ℤ' :
  (x y z : ℤ) → Id (diff-ℤ (mul-ℤ x z) (mul-ℤ y z)) (mul-ℤ (diff-ℤ x y) z)
linear-diff-ℤ' x y z =
  ( ap (add-ℤ (mul-ℤ x z)) (inv (left-negative-law-mul-ℤ y z))) ∙
  ( inv (right-distributive-mul-add-ℤ x (neg-ℤ y) z))
```
