---
title: Magmas
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module wild-algebra.magmas where

open import elementary-number-theory.natural-numbers using (ℕ; zero-ℕ; succ-ℕ)

open import foundation.cartesian-product-types using (_×_)
open import foundation.coproduct-types using (coprod; inl; inr)
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.equivalences using (_≃_; map-equiv)
open import foundation.functions using (_∘_)
open import foundation.identity-types using (Id)
open import foundation.unit-type using (unit; star)
open import foundation.universe-levels using (Level; UU; lsuc)

open import univalent-combinatorics.counting using (count; map-equiv-count)
open import univalent-combinatorics.standard-finite-types using (Fin)
```

## Idea

A magma is a type equipped with a binary operation.

## Definition

```agda
Magma : (l : Level) → UU (lsuc l)
Magma l = Σ (UU l) (λ A → A → A → A)

module _
  {l : Level} (M : Magma l)
  where
  
  type-Magma : UU l
  type-Magma = pr1 M
  
  mul-Magma : type-Magma → type-Magma → type-Magma
  mul-Magma = pr2 M
  
  mul-Magma' : type-Magma → type-Magma → type-Magma
  mul-Magma' x y = mul-Magma y x
```

## Structures

### The fold operation on magmas

```agda
fold-Fin-mul-Magma :
  {l : Level} (M : Magma l) → type-Magma M →
  {k : ℕ} → (Fin k → type-Magma M) → type-Magma M
fold-Fin-mul-Magma M m {zero-ℕ} f = m
fold-Fin-mul-Magma M m {succ-ℕ k} f =
  mul-Magma M (fold-Fin-mul-Magma M m (f ∘ inl)) (f (inr star))

fold-count-mul-Magma' :
  {l1 l2 : Level} (M : Magma l1) → type-Magma M →
  {A : UU l2} {k : ℕ} → (Fin k ≃ A) → (A → type-Magma M) → type-Magma M
fold-count-mul-Magma' M m e f = fold-Fin-mul-Magma M m (f ∘ map-equiv e)

fold-count-mul-Magma :
  {l1 l2 : Level} (M : Magma l1) → type-Magma M →
  {A : UU l2} → count A → (A → type-Magma M) → type-Magma M
fold-count-mul-Magma M m e f = fold-Fin-mul-Magma M m (f ∘ map-equiv-count e)
```

### Unital magmas

```agda
is-unital-Magma : {l : Level} (M : Magma l) → UU l
is-unital-Magma M =
  Σ ( type-Magma M)
    ( λ e →
      ( (x : type-Magma M) → Id (mul-Magma M e x) x) ×
      ( (x : type-Magma M) → Id (mul-Magma M x e) x))

Unital-Magma : (l : Level) → UU (lsuc l)
Unital-Magma l = Σ (Magma l) is-unital-Magma

magma-Unital-Magma :
  {l : Level} → Unital-Magma l → Magma l
magma-Unital-Magma M = pr1 M
  
is-unital-magma-Unital-Magma :
  {l : Level} (M : Unital-Magma l) → is-unital-Magma (magma-Unital-Magma M)
is-unital-magma-Unital-Magma M = pr2 M
```

### Semigroups

```agda
is-semigroup-Magma : {l : Level} → Magma l → UU l
is-semigroup-Magma M =
  (x y z : type-Magma M) →
  Id (mul-Magma M (mul-Magma M x y) z) (mul-Magma M x (mul-Magma M y z))
```

### Commutative magmas

```agda
is-commutative-Magma : {l : Level} → Magma l → UU l
is-commutative-Magma M =
  (x y : type-Magma M) → Id (mul-Magma M x y) (mul-Magma M y x)
```

### The structure of a commutative monoid on magmas

```agda
is-commutative-monoid-Magma : {l : Level} → Magma l → UU l
is-commutative-monoid-Magma M =
  ((is-semigroup-Magma M) × (is-unital-Magma M)) × (is-commutative-Magma M)

unit-is-commutative-monoid-Magma :
  {l : Level} (M : Magma l) → is-commutative-monoid-Magma M → type-Magma M
unit-is-commutative-monoid-Magma M H = pr1 (pr2 (pr1 H))
```
