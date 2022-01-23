---
title: Univalent Mathematics in Agda
---

```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module foundations.natural-numbers where

open import foundations.cartesian-product-types using (_×_)
open import foundations.coproduct-types using (inl; inr)
open import foundations.decidable-types using
  ( is-decidable; has-decidable-equality; is-decidable-iff; is-decidable-neg)
open import foundations.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundations.empty-type using (empty; ex-falso)
open import foundations.functions using (id; _∘_)
open import foundations.identity-types using (Id; refl; _∙_; inv; ap; ap-binary)
open import foundations.injective-maps using (is-injective)
open import foundations.laws-for-operations using
  ( interchange-law; interchange-law-commutative-and-associative)
open import foundations.levels using (Level; lzero; UU)
open import foundations.logical-equivalence using (_↔_)
open import foundations.negation using (¬)
open import foundations.unit-type using (unit; star)
```

# The type of natural numbers

```agda
data ℕ : UU lzero where
  zero-ℕ : ℕ
  succ-ℕ : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}
```

## The induction principle of ℕ

```agda
ind-ℕ :
  {i : Level} {P : ℕ → UU i} →
  P 0 → ((n : ℕ) → P n → P(succ-ℕ n)) → ((n : ℕ) → P n)
ind-ℕ p0 pS 0 = p0
ind-ℕ p0 pS (succ-ℕ n) = pS n (ind-ℕ p0 pS n)
```

### Asserting (in)equality to 0 and 1

```agda
is-zero-ℕ : ℕ → UU lzero
is-zero-ℕ n = Id n zero-ℕ

is-zero-ℕ' : ℕ → UU lzero
is-zero-ℕ' n = Id zero-ℕ n

is-successor-ℕ : ℕ → UU lzero
is-successor-ℕ n = Σ ℕ (λ y → Id n (succ-ℕ y))

is-nonzero-ℕ : ℕ → UU lzero
is-nonzero-ℕ n = ¬ (is-zero-ℕ n)

is-one-ℕ : ℕ → UU lzero
is-one-ℕ n = Id n 1

is-one-ℕ' : ℕ → UU lzero
is-one-ℕ' n = Id 1 n

is-not-one-ℕ : ℕ → UU lzero
is-not-one-ℕ n = ¬ (is-one-ℕ n)

is-not-one-ℕ' : ℕ → UU lzero
is-not-one-ℕ' n = ¬ (is-one-ℕ' n)
```

## Observational equality on the natural numbers

```agda
Eq-ℕ : ℕ → ℕ → UU lzero
Eq-ℕ zero-ℕ zero-ℕ = unit
Eq-ℕ zero-ℕ (succ-ℕ n) = empty
Eq-ℕ (succ-ℕ m) zero-ℕ = empty
Eq-ℕ (succ-ℕ m) (succ-ℕ n) = Eq-ℕ m n

refl-Eq-ℕ : (n : ℕ) → Eq-ℕ n n
refl-Eq-ℕ zero-ℕ = star
refl-Eq-ℕ (succ-ℕ n) = refl-Eq-ℕ n

Eq-eq-ℕ : {x y : ℕ} → Id x y → Eq-ℕ x y
Eq-eq-ℕ {x} {.x} refl = refl-Eq-ℕ x

eq-Eq-ℕ : (x y : ℕ) → Eq-ℕ x y → Id x y
eq-Eq-ℕ zero-ℕ zero-ℕ e = refl
eq-Eq-ℕ (succ-ℕ x) (succ-ℕ y) e = ap succ-ℕ (eq-Eq-ℕ x y e)

is-decidable-Eq-ℕ :
  (m n : ℕ) → is-decidable (Eq-ℕ m n)
is-decidable-Eq-ℕ zero-ℕ zero-ℕ = inl star
is-decidable-Eq-ℕ zero-ℕ (succ-ℕ n) = inr id
is-decidable-Eq-ℕ (succ-ℕ m) zero-ℕ = inr id
is-decidable-Eq-ℕ (succ-ℕ m) (succ-ℕ n) = is-decidable-Eq-ℕ m n

has-decidable-equality-ℕ : has-decidable-equality ℕ
has-decidable-equality-ℕ x y =
  is-decidable-iff (eq-Eq-ℕ x y) Eq-eq-ℕ (is-decidable-Eq-ℕ x y)

is-decidable-is-zero-ℕ : (n : ℕ) → is-decidable (is-zero-ℕ n)
is-decidable-is-zero-ℕ n = has-decidable-equality-ℕ n zero-ℕ

is-decidable-is-zero-ℕ' : (n : ℕ) → is-decidable (is-zero-ℕ' n)
is-decidable-is-zero-ℕ' n = has-decidable-equality-ℕ zero-ℕ n

is-decidable-is-nonzero-ℕ : (n : ℕ) → is-decidable (is-nonzero-ℕ n)
is-decidable-is-nonzero-ℕ n =
  is-decidable-neg (is-decidable-is-zero-ℕ n)

is-decidable-is-one-ℕ : (n : ℕ) → is-decidable (is-one-ℕ n)
is-decidable-is-one-ℕ n = has-decidable-equality-ℕ n 1

is-decidable-is-one-ℕ' : (n : ℕ) → is-decidable (is-one-ℕ' n)
is-decidable-is-one-ℕ' n = has-decidable-equality-ℕ 1 n

is-decidable-is-not-one-ℕ :
  (x : ℕ) → is-decidable (is-not-one-ℕ x)
is-decidable-is-not-one-ℕ x =
  is-decidable-neg (is-decidable-is-one-ℕ x)
```

### The successor function on ℕ is injective

```agda
is-injective-succ-ℕ : is-injective succ-ℕ
is-injective-succ-ℕ refl = refl
```

## Peano's 7th and 8th axioms

```agda
Peano-7 :
  (x y : ℕ) → (Id x y) ↔ (Id (succ-ℕ x) (succ-ℕ y))
pr1 (Peano-7 x y) = ap succ-ℕ
pr2 (Peano-7 x y) = is-injective-succ-ℕ

Peano-8 : (x : ℕ) → is-nonzero-ℕ (succ-ℕ x)
Peano-8 x ()

is-nonzero-succ-ℕ : (x : ℕ) → is-nonzero-ℕ (succ-ℕ x)
is-nonzero-succ-ℕ x ()

is-nonzero-is-successor-ℕ : {x : ℕ} → is-successor-ℕ x → is-nonzero-ℕ x
is-nonzero-is-successor-ℕ (pair x refl) ()

is-successor-is-nonzero-ℕ : {x : ℕ} → is-nonzero-ℕ x → is-successor-ℕ x
is-successor-is-nonzero-ℕ {zero-ℕ} H = ex-falso (H refl)
pr1 (is-successor-is-nonzero-ℕ {succ-ℕ x} H) = x
pr2 (is-successor-is-nonzero-ℕ {succ-ℕ x} H) = refl

is-nonzero-one-ℕ : is-nonzero-ℕ 1
is-nonzero-one-ℕ ()

is-not-one-zero-ℕ : is-not-one-ℕ zero-ℕ
is-not-one-zero-ℕ ()

is-not-one-two-ℕ : is-not-one-ℕ 2
is-not-one-two-ℕ ()

has-no-fixed-points-succ-ℕ : (x : ℕ) → ¬ (Id (succ-ℕ x) x)
has-no-fixed-points-succ-ℕ x ()
```
