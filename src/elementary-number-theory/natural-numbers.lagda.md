---
title: Univalent Mathematics in Agda
---

# Natural numbers

```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module elementary-number-theory.natural-numbers where

open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundations.empty-type using (ex-falso)
open import foundation.identity-types using (Id; refl)
open import foundation.injective-maps using (is-injective)
open import foundation.levels using (Level; lzero; UU)
open import foundations.logical-equivalence using (_↔_)
open import foundations.negation using (¬)
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

## Useful predicates on the natural numbers

These predicates can of course be asserted directly without much trouble. However, using the defined predicates ensures uniformity, and helps naming definitions.

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

is-nonzero-one-ℕ : is-nonzero-ℕ 1
is-nonzero-one-ℕ ()

is-not-one-zero-ℕ : is-not-one-ℕ zero-ℕ
is-not-one-zero-ℕ ()

is-not-one-two-ℕ : is-not-one-ℕ 2
is-not-one-two-ℕ ()
```

## Peano's 7th axiom

```agda
is-injective-succ-ℕ : is-injective succ-ℕ
is-injective-succ-ℕ refl = refl

private
  Peano-7 :
    (x y : ℕ) → (Id x y) ↔ (Id (succ-ℕ x) (succ-ℕ y))
  pr1 (Peano-7 x y) refl = refl
  pr2 (Peano-7 x y) = is-injective-succ-ℕ
```

## Peano's 8th axiom

```agda
private   
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

has-no-fixed-points-succ-ℕ : (x : ℕ) → ¬ (Id (succ-ℕ x) x)
has-no-fixed-points-succ-ℕ x ()
```
