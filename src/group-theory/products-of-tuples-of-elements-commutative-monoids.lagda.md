---
title: Products of tuples of elements in commutative monoids
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module group-theory.products-of-tuples-of-elements-commutative-monoids where

open import elementary-number-theory.natural-numbers

open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.functions
open import foundation.identity-types
open import foundation.unit-type
open import foundation.universe-levels

open import group-theory.commutative-monoids
open import group-theory.unordered-tuples-of-elements-commutative-monoids

open import univalent-combinatorics.counting
open import univalent-combinatorics.standard-finite-types
```

## Idea

Given an unordered n-tuple of elements in a commutative monoid, we can define their product

## Definition

### Products of ordered n-tuples of elements in commutative monoids

```agda
module _
  {l : Level} (M : Commutative-Monoid l)
  where

  mul-fin-Commutative-Monoid :
    (n : ℕ) → (Fin n → type-Commutative-Monoid M) → type-Commutative-Monoid M
  mul-fin-Commutative-Monoid zero-ℕ x = unit-Commutative-Monoid M
  mul-fin-Commutative-Monoid (succ-ℕ n) x =
    mul-Commutative-Monoid M
      ( mul-fin-Commutative-Monoid n (x ∘ inl))
      ( x (inr star))

  compute-permutation-mul-fin-Commutative-Monoid :
    (n : ℕ) (e : Fin n ≃ Fin n) (x : Fin n → type-Commutative-Monoid M) →
    Id ( mul-fin-Commutative-Monoid n (x ∘ map-equiv e))
       ( mul-fin-Commutative-Monoid n x)
  compute-permutation-mul-fin-Commutative-Monoid n e x = ?

  mul-count-Commutative-Monoid :
    {l2 : Level} {A : UU l2} → count A →
    (A → type-Commutative-Monoid M) → type-Commutative-Monoid M
  mul-count-Commutative-Monoid e x =
    mul-fin-Commutative-Monoid
      ( number-of-elements-count e)
      ( x ∘ map-equiv-count e)

  compute-mul-double-counting-Commutative-Monoid :
    {l2 : Level} {A : UU l2} (e1 : count A) (e2 : count A) →
    (x : A → type-Commutative-Monoid M) →
    Id (mul-count-Commutative-Monoid e1 x) (mul-count-Commutative-Monoid e2 x)
  compute-mul-double-counting-Commutative-Monoid e1 e2 x = {!!}
```

### Products of unordered n-tuples of elements in commutative monoids

```agda
module _
  {l : Level} (M : Commutative-Monoid l)
  where
  
  mul-tuple-Commutative-Monoid :
    {n : ℕ} → unordered-tuple-Commutative-Monoid n M → type-Commutative-Monoid M
  mul-tuple-Commutative-Monoid {n} (pair I x) = {!!}
```
