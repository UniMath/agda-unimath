---
title: Univalent Mathematics in Agda
---

# The absolute value function on the integers

```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module elementary-number-theory.absolute-value-integers where

open import elementary-number-theory.addition-integers using
  ( add-ℤ; add-neg-one-right-ℤ; right-predecessor-law-add-ℤ;
    right-unit-law-add-ℤ; add-one-right-ℤ; right-successor-law-add-ℤ)
open import elementary-number-theory.addition-natural-numbers using (add-ℕ)
open import elementary-number-theory.inequality-natural-numbers using
  (_≤-ℕ_; refl-leq-ℕ; preserves-leq-succ-ℕ; succ-leq-ℕ;
    concatenate-eq-leq-eq-ℕ; transitive-leq-ℕ)
open import elementary-number-theory.integers using
  ( ℤ; int-ℕ; neg-ℤ; zero-ℤ; is-zero-ℤ; succ-ℤ; pred-ℤ; is-positive-ℤ)
open import elementary-number-theory.natural-numbers using
  ( ℕ; zero-ℕ; succ-ℕ; is-zero-ℕ; is-nonzero-ℕ; is-nonzero-succ-ℕ)
open import foundation.coproduct-types using (inl; inr)
open import foundation.empty-types using (ex-falso)
open import foundation.functions using (_∘_)
open import foundation.identity-types using (Id; refl; ap)
open import foundation.unit-type using (star)
```

# The absolute value of integers

```
abs-ℤ : ℤ → ℕ
abs-ℤ (inl x) = succ-ℕ x
abs-ℤ (inr (inl star)) = zero-ℕ
abs-ℤ (inr (inr x)) = succ-ℕ x

int-abs-ℤ : ℤ → ℤ
int-abs-ℤ = int-ℕ ∘ abs-ℤ

abs-int-ℕ : (x : ℕ) → Id (abs-ℤ (int-ℕ x)) x
abs-int-ℕ zero-ℕ = refl
abs-int-ℕ (succ-ℕ x) = refl

abs-neg-ℤ : (x : ℤ) → Id (abs-ℤ (neg-ℤ x)) (abs-ℤ x)
abs-neg-ℤ (inl x) = refl
abs-neg-ℤ (inr (inl star)) = refl
abs-neg-ℤ (inr (inr x)) = refl

eq-abs-ℤ : (x : ℤ) → is-zero-ℕ (abs-ℤ x) → is-zero-ℤ x
eq-abs-ℤ (inr (inl star)) p = refl

abs-eq-ℤ : (x : ℤ) → is-zero-ℤ x → is-zero-ℕ (abs-ℤ x)
abs-eq-ℤ .zero-ℤ refl = refl

predecessor-law-abs-ℤ :
  (x : ℤ) → (abs-ℤ (pred-ℤ x)) ≤-ℕ (succ-ℕ (abs-ℤ x))
predecessor-law-abs-ℤ (inl x) =
  refl-leq-ℕ (succ-ℕ x)
predecessor-law-abs-ℤ (inr (inl star)) =
  refl-leq-ℕ zero-ℕ
predecessor-law-abs-ℤ (inr (inr zero-ℕ)) =
  star
predecessor-law-abs-ℤ (inr (inr (succ-ℕ x))) =
  preserves-leq-succ-ℕ x (succ-ℕ x) (succ-leq-ℕ x)

successor-law-abs-ℤ :
  (x : ℤ) → (abs-ℤ (succ-ℤ x)) ≤-ℕ (succ-ℕ (abs-ℤ x))
successor-law-abs-ℤ (inl zero-ℕ) =
  star
successor-law-abs-ℤ (inl (succ-ℕ x)) =
  preserves-leq-succ-ℕ x (succ-ℕ x) (succ-leq-ℕ x)
successor-law-abs-ℤ (inr (inl star)) =
  refl-leq-ℕ zero-ℕ
successor-law-abs-ℤ (inr (inr x)) =
  refl-leq-ℕ (succ-ℕ x)

subadditive-abs-ℤ :
  (x y : ℤ) → (abs-ℤ (add-ℤ x y)) ≤-ℕ (add-ℕ (abs-ℤ x) (abs-ℤ y))
subadditive-abs-ℤ x (inl zero-ℕ) =
  concatenate-eq-leq-eq-ℕ
    ( ap abs-ℤ (add-neg-one-right-ℤ x))
    ( predecessor-law-abs-ℤ x)
    ( refl)
subadditive-abs-ℤ x (inl (succ-ℕ y)) =
  concatenate-eq-leq-eq-ℕ
    ( ap abs-ℤ (right-predecessor-law-add-ℤ x (inl y)))
    ( transitive-leq-ℕ
      ( abs-ℤ (pred-ℤ (add-ℤ x (inl y))))
      ( succ-ℕ (abs-ℤ (add-ℤ x (inl y))))
      ( add-ℕ (abs-ℤ x) (succ-ℕ (succ-ℕ y)))
      ( predecessor-law-abs-ℤ (add-ℤ x (inl y)))
      ( subadditive-abs-ℤ x (inl y)))
    ( refl)
subadditive-abs-ℤ x (inr (inl star)) =
  concatenate-eq-leq-eq-ℕ
    ( ap abs-ℤ (right-unit-law-add-ℤ x))
    ( refl-leq-ℕ (abs-ℤ x))
    ( refl)
subadditive-abs-ℤ x (inr (inr zero-ℕ)) =
  concatenate-eq-leq-eq-ℕ
    ( ap abs-ℤ (add-one-right-ℤ x))
    ( successor-law-abs-ℤ x)
    ( refl)
subadditive-abs-ℤ x (inr (inr (succ-ℕ y))) =
  concatenate-eq-leq-eq-ℕ
    ( ap abs-ℤ (right-successor-law-add-ℤ x (inr (inr y))))
    ( transitive-leq-ℕ
      ( abs-ℤ (succ-ℤ (add-ℤ x (inr (inr y)))))
      ( succ-ℕ (abs-ℤ (add-ℤ x (inr (inr y)))))
      ( succ-ℕ (add-ℕ (abs-ℤ x) (succ-ℕ y)))
      ( successor-law-abs-ℤ (add-ℤ x (inr (inr y))))
      ( subadditive-abs-ℤ x (inr (inr y))))
    ( refl)

negative-law-abs-ℤ :
  (x : ℤ) → Id (abs-ℤ (neg-ℤ x)) (abs-ℤ x)
negative-law-abs-ℤ (inl x) = refl
negative-law-abs-ℤ (inr (inl star)) = refl
negative-law-abs-ℤ (inr (inr x)) = refl

is-positive-abs-ℤ :
  (x : ℤ) → is-positive-ℤ x → is-positive-ℤ (int-abs-ℤ x)
is-positive-abs-ℤ (inr (inr x)) H = star

is-nonzero-abs-ℤ :
  (x : ℤ) → is-positive-ℤ x → is-nonzero-ℕ (abs-ℤ x)
is-nonzero-abs-ℤ (inr (inr x)) H = is-nonzero-succ-ℕ x
```
