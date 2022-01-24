---
title: Univalent Mathematics in Agda
---

```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module foundations.integers where

open import foundations.coproduct-types using (coprod; inl; inr)
open import foundations.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundations.empty-type using (empty; ex-falso)
open import foundations.functions using (id)
open import foundations.identity-types using (Id; refl; _∙_; inv; ap)
open import foundations.injective-maps using (is-injective)
open import foundations.levels using (UU; Level; lzero)
open import foundations.natural-numbers using
  ( ℕ; zero-ℕ; succ-ℕ; is-nonzero-ℕ)
open import foundations.negation using (¬)
open import foundations.unit-type using (unit; star)
```

## The type of integers

```agda
ℤ : UU lzero
ℤ = coprod ℕ (coprod unit ℕ)
```

## Inclusion of the negative integers

```agda
in-neg : ℕ → ℤ
in-neg n = inl n

neg-one-ℤ : ℤ
neg-one-ℤ = in-neg zero-ℕ

is-neg-one-ℤ : ℤ → UU lzero
is-neg-one-ℤ x = Id x neg-one-ℤ
```

## Zero

```agda
zero-ℤ : ℤ
zero-ℤ = inr (inl star)

is-zero-ℤ : ℤ → UU lzero
is-zero-ℤ x = Id x zero-ℤ

is-nonzero-ℤ : ℤ → UU lzero
is-nonzero-ℤ k = ¬ (is-zero-ℤ k)
```

## Inclusion of the positive integers

```agda
in-pos : ℕ → ℤ
in-pos n = inr (inr n)

one-ℤ : ℤ
one-ℤ = in-pos zero-ℕ

is-one-ℤ : ℤ → UU lzero
is-one-ℤ x = Id x one-ℤ
```

- Inclusion of the natural numbers

```agda
int-ℕ : ℕ → ℤ
int-ℕ zero-ℕ = zero-ℤ
int-ℕ (succ-ℕ n) = in-pos n

is-injective-int-ℕ : is-injective int-ℕ
is-injective-int-ℕ {zero-ℕ} {zero-ℕ} refl = refl
is-injective-int-ℕ {succ-ℕ x} {succ-ℕ y} refl = refl

is-nonzero-int-ℕ : (n : ℕ) → is-nonzero-ℕ n → is-nonzero-ℤ (int-ℕ n)
is-nonzero-int-ℕ zero-ℕ H p = H refl
```

- Induction principle on the type of integers

```agda
ind-ℤ :
  {l : Level} (P : ℤ → UU l) →
  P neg-one-ℤ → ((n : ℕ) → P (inl n) → P (inl (succ-ℕ n))) →
  P zero-ℤ →
  P one-ℤ → ((n : ℕ) → P (inr (inr (n))) → P (inr (inr (succ-ℕ n)))) →
  (k : ℤ) → P k
ind-ℤ P p-1 p-S p0 p1 pS (inl zero-ℕ) = p-1
ind-ℤ P p-1 p-S p0 p1 pS (inl (succ-ℕ x)) =
  p-S x (ind-ℤ P p-1 p-S p0 p1 pS (inl x))
ind-ℤ P p-1 p-S p0 p1 pS (inr (inl star)) = p0
ind-ℤ P p-1 p-S p0 p1 pS (inr (inr zero-ℕ)) = p1
ind-ℤ P p-1 p-S p0 p1 pS (inr (inr (succ-ℕ x))) =
  pS x (ind-ℤ P p-1 p-S p0 p1 pS (inr (inr (x))))
```

- The successor and predecessor functions on ℤ

```agda
succ-ℤ : ℤ → ℤ
succ-ℤ (inl zero-ℕ) = zero-ℤ
succ-ℤ (inl (succ-ℕ x)) = inl x
succ-ℤ (inr (inl star)) = one-ℤ
succ-ℤ (inr (inr x)) = inr (inr (succ-ℕ x))

pred-ℤ : ℤ → ℤ
pred-ℤ (inl x) = inl (succ-ℕ x)
pred-ℤ (inr (inl star)) = inl zero-ℕ
pred-ℤ (inr (inr zero-ℕ)) = inr (inl star)
pred-ℤ (inr (inr (succ-ℕ x))) = inr (inr x)
```
- The negative of an integer

```agda
neg-ℤ : ℤ → ℤ
neg-ℤ (inl x) = inr (inr x)
neg-ℤ (inr (inl star)) = inr (inl star)
neg-ℤ (inr (inr x)) = inl x
```

## The successor and predecessor functions on ℤ are mutual inverses

```agda
abstract
  isretr-pred-ℤ :
    (k : ℤ) → Id (pred-ℤ (succ-ℤ k)) k
  isretr-pred-ℤ (inl zero-ℕ) = refl
  isretr-pred-ℤ (inl (succ-ℕ x)) = refl
  isretr-pred-ℤ (inr (inl star)) = refl
  isretr-pred-ℤ (inr (inr zero-ℕ)) = refl
  isretr-pred-ℤ (inr (inr (succ-ℕ x))) = refl
  
  issec-pred-ℤ :
    (k : ℤ) → Id (succ-ℤ (pred-ℤ k)) k
  issec-pred-ℤ (inl zero-ℕ) = refl
  issec-pred-ℤ (inl (succ-ℕ x)) = refl
  issec-pred-ℤ (inr (inl star)) = refl
  issec-pred-ℤ (inr (inr zero-ℕ)) = refl
  issec-pred-ℤ (inr (inr (succ-ℕ x))) = refl
```

### The successor function on ℤ is injective

```agda
  is-injective-succ-ℤ : is-injective succ-ℤ
  is-injective-succ-ℤ {x} {y} p =
    inv (isretr-pred-ℤ x) ∙ (ap pred-ℤ p ∙ isretr-pred-ℤ y)
```

```agda
neg-neg-ℤ : (k : ℤ) → Id (neg-ℤ (neg-ℤ k)) k
neg-neg-ℤ (inl n) = refl
neg-neg-ℤ (inr (inl star)) = refl
neg-neg-ℤ (inr (inr n)) = refl

neg-pred-ℤ : (k : ℤ) → Id (neg-ℤ (pred-ℤ k)) (succ-ℤ (neg-ℤ k))
neg-pred-ℤ (inl x) = refl
neg-pred-ℤ (inr (inl star)) = refl
neg-pred-ℤ (inr (inr zero-ℕ)) = refl
neg-pred-ℤ (inr (inr (succ-ℕ x))) = refl

neg-succ-ℤ : (x : ℤ) → Id (neg-ℤ (succ-ℤ x)) (pred-ℤ (neg-ℤ x))
neg-succ-ℤ (inl zero-ℕ) = refl
neg-succ-ℤ (inl (succ-ℕ x)) = refl
neg-succ-ℤ (inr (inl star)) = refl
neg-succ-ℤ (inr (inr x)) = refl

pred-neg-ℤ :
  (k : ℤ) → Id (pred-ℤ (neg-ℤ k)) (neg-ℤ (succ-ℤ k))
pred-neg-ℤ (inl zero-ℕ) = refl
pred-neg-ℤ (inl (succ-ℕ x)) = refl
pred-neg-ℤ (inr (inl star)) = refl
pred-neg-ℤ (inr (inr x)) = refl
```

## Negative and positive integers

```
is-nonnegative-ℤ : ℤ → UU lzero
is-nonnegative-ℤ (inl x) = empty
is-nonnegative-ℤ (inr k) = unit

is-nonnegative-eq-ℤ :
  {x y : ℤ} → Id x y → is-nonnegative-ℤ x → is-nonnegative-ℤ y
is-nonnegative-eq-ℤ refl = id

is-zero-is-nonnegative-ℤ :
  {x : ℤ} → is-nonnegative-ℤ x → is-nonnegative-ℤ (neg-ℤ x) → is-zero-ℤ x
is-zero-is-nonnegative-ℤ {inr (inl star)} H K = refl

is-nonnegative-succ-ℤ :
  (k : ℤ) → is-nonnegative-ℤ k → is-nonnegative-ℤ (succ-ℤ k)
is-nonnegative-succ-ℤ (inr (inl star)) p = star
is-nonnegative-succ-ℤ (inr (inr x)) p = star

-- We introduce positive integers

is-positive-ℤ : ℤ → UU lzero
is-positive-ℤ (inl x) = empty
is-positive-ℤ (inr (inl x)) = empty
is-positive-ℤ (inr (inr x)) = unit

positive-ℤ : UU lzero
positive-ℤ = Σ ℤ is-positive-ℤ

is-nonnegative-is-positive-ℤ : {x : ℤ} → is-positive-ℤ x → is-nonnegative-ℤ x
is-nonnegative-is-positive-ℤ {inr (inr x)} H = H

is-nonzero-is-positive-ℤ : (x : ℤ) → is-positive-ℤ x → is-nonzero-ℤ x
is-nonzero-is-positive-ℤ (inr (inr x)) H ()

is-positive-eq-ℤ : {x y : ℤ} → Id x y → is-positive-ℤ x → is-positive-ℤ y
is-positive-eq-ℤ {x} refl = id

is-positive-one-ℤ : is-positive-ℤ one-ℤ
is-positive-one-ℤ = star

one-positive-ℤ : positive-ℤ
pr1 one-positive-ℤ = one-ℤ
pr2 one-positive-ℤ = is-positive-one-ℤ

is-positive-succ-ℤ : {x : ℤ} → is-nonnegative-ℤ x → is-positive-ℤ (succ-ℤ x)
is-positive-succ-ℤ {inr (inl star)} H = is-positive-one-ℤ
is-positive-succ-ℤ {inr (inr x)} H = star

is-positive-int-ℕ :
  (x : ℕ) → is-nonzero-ℕ x → is-positive-ℤ (int-ℕ x)
is-positive-int-ℕ zero-ℕ H = ex-falso (H refl)
is-positive-int-ℕ (succ-ℕ x) H = star

-- Basics of nonnegative integers

nonnegative-ℤ : UU lzero
nonnegative-ℤ = Σ ℤ is-nonnegative-ℤ

int-nonnegative-ℤ : nonnegative-ℤ → ℤ
int-nonnegative-ℤ = pr1

is-nonnegative-int-nonnegative-ℤ :
  (x : nonnegative-ℤ) → is-nonnegative-ℤ (int-nonnegative-ℤ x)
is-nonnegative-int-nonnegative-ℤ = pr2

is-injective-int-nonnegative-ℤ : is-injective int-nonnegative-ℤ
is-injective-int-nonnegative-ℤ {pair (inr x) star} {pair (inr .x) star} refl =
  refl

is-nonnegative-int-ℕ : (n : ℕ) → is-nonnegative-ℤ (int-ℕ n)
is-nonnegative-int-ℕ zero-ℕ = star
is-nonnegative-int-ℕ (succ-ℕ n) = star

nonnegative-int-ℕ : ℕ → nonnegative-ℤ
pr1 (nonnegative-int-ℕ n) = int-ℕ n
pr2 (nonnegative-int-ℕ n) = is-nonnegative-int-ℕ n

nat-nonnegative-ℤ : nonnegative-ℤ → ℕ
nat-nonnegative-ℤ (pair (inr (inl x)) H) = zero-ℕ
nat-nonnegative-ℤ (pair (inr (inr x)) H) = succ-ℕ x

issec-nat-nonnegative-ℤ :
  (x : nonnegative-ℤ) → Id (nonnegative-int-ℕ (nat-nonnegative-ℤ x)) x
issec-nat-nonnegative-ℤ (pair (inr (inl star)) star) = refl
issec-nat-nonnegative-ℤ (pair (inr (inr x)) star) = refl

isretr-nat-nonnegative-ℤ :
  (n : ℕ) → Id (nat-nonnegative-ℤ (nonnegative-int-ℕ n)) n
isretr-nat-nonnegative-ℤ zero-ℕ = refl
isretr-nat-nonnegative-ℤ (succ-ℕ n) = refl

is-injective-nonnegative-int-ℕ : is-injective nonnegative-int-ℕ
is-injective-nonnegative-int-ℕ {x} {y} p =
  ( inv (isretr-nat-nonnegative-ℤ x)) ∙
  ( ( ap nat-nonnegative-ℤ p) ∙
    ( isretr-nat-nonnegative-ℤ y))

decide-is-nonnegative-ℤ :
  {x : ℤ} → coprod (is-nonnegative-ℤ x) (is-nonnegative-ℤ (neg-ℤ x))
decide-is-nonnegative-ℤ {inl x} = inr star
decide-is-nonnegative-ℤ {inr x} = inl star
```
