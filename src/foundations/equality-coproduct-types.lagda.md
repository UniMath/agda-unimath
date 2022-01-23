---
title: Univalent Mathematics in Agda
---

```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module foundations.equality-coproduct-types where

open import foundations.coproduct-types using (coprod; inl; inr)
open import foundations.decidable-types using
  ( has-decidable-equality; is-decidable-iff)
open import foundations.levels using (Level; UU; _⊔_)
open import foundations.identity-types using (Id; refl; ap)
open import foundations.injective-maps using (is-injective)
open import foundations.negation using (¬)
```

## Observational equality of coproduct types

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  data Eq-coprod : coprod A B → coprod A B → UU (l1 ⊔ l2)
    where
    Eq-eq-coprod-inl : {x y : A} → Id x y → Eq-coprod (inl x) (inl y)
    Eq-eq-coprod-inr : {x y : B} → Id x y → Eq-coprod (inr x) (inr y)

  refl-Eq-coprod : (x : coprod A B) → Eq-coprod x x
  refl-Eq-coprod (inl x) = Eq-eq-coprod-inl refl
  refl-Eq-coprod (inr x) = Eq-eq-coprod-inr refl

  Eq-eq-coprod : (x y : coprod A B) → Id x y → Eq-coprod x y
  Eq-eq-coprod x .x refl = refl-Eq-coprod x

  eq-Eq-coprod : (x y : coprod A B) → Eq-coprod x y → Id x y
  eq-Eq-coprod .(inl x) .(inl x) (Eq-eq-coprod-inl {x} {.x} refl) = refl
  eq-Eq-coprod .(inr x) .(inr x) (Eq-eq-coprod-inr {x} {.x} refl) = refl

  is-injective-inl : is-injective {B = coprod A B} inl
  is-injective-inl refl = refl

  is-injective-inr : is-injective {B = coprod A B} inr
  is-injective-inr refl = refl 

  neq-inl-inr :
    (x : A) (y : B) → ¬ (Id (inl x) (inr y))
  neq-inl-inr x y ()

  neq-inr-inl :
    (x : B) (y : A) → ¬ (Id (inr x) (inl y))
  neq-inr-inl x y ()
  
  has-decidable-equality-coprod :
    has-decidable-equality A → has-decidable-equality B →
    has-decidable-equality (coprod A B)
  has-decidable-equality-coprod d e (inl x) (inl y) =
    is-decidable-iff (ap inl) is-injective-inl (d x y)
  has-decidable-equality-coprod d e (inl x) (inr y) =
    inr (neq-inl-inr x y)
  has-decidable-equality-coprod d e (inr x) (inl y) =
    inr (neq-inr-inl x y)
  has-decidable-equality-coprod d e (inr x) (inr y) =
    is-decidable-iff (ap inr) is-injective-inr (e x y)

  has-decidable-equality-left-summand :
    has-decidable-equality (coprod A B) → has-decidable-equality A
  has-decidable-equality-left-summand d x y =
    is-decidable-iff is-injective-inl (ap inl) (d (inl x) (inl y))

  has-decidable-equality-right-summand :
    has-decidable-equality (coprod A B) → has-decidable-equality B
  has-decidable-equality-right-summand d x y =
    is-decidable-iff is-injective-inr (ap inr) (d (inr x) (inr y))
```
