---
title: Non-contractible types
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation.non-contractible-types where

open import elementary-number-theory.natural-numbers using (ℕ; zero-ℕ; succ-ℕ)

open import foundation.contractible-types using
  ( is-contr; center; contraction; is-prop-is-contr)
open import foundation.dependent-pair-types using (Σ; pair)
open import foundation.empty-types using (is-empty; empty)
open import foundation.functions using (id)
open import foundation.identity-types using (_＝_)
open import foundation.negation using (¬)
open import foundation.universe-levels using (Level; UU)
```

## Idea

A type `X` is non-contractible if it comes equipped with an element of type `¬ (is-contr X)`.

## Definitions

### The negation of being contractible

```agda
is-not-contractible : {l : Level} → UU l → UU l
is-not-contractible X = ¬ (is-contr X)
```

### A positive formulation of being noncontractible

```agda
is-noncontractible' : {l : Level} (A : UU l) → ℕ → UU l
is-noncontractible' A zero-ℕ = is-empty A
is-noncontractible' A (succ-ℕ k) =
  Σ A (λ x → Σ A (λ y → is-noncontractible' (x ＝ y) k))
 
is-noncontractible : {l : Level} (A : UU l) → UU l
is-noncontractible A = Σ ℕ (is-noncontractible' A)
```

## Properties

### Empty types are not contractible

```agda
is-not-contractible-is-empty :
  {l : Level} {X : UU l} → is-empty X → is-not-contractible X
is-not-contractible-is-empty H C = H (center C)

is-not-contractible-empty : is-not-contractible empty
is-not-contractible-empty = is-not-contractible-is-empty id
```

### Noncontractible types are not contractible

```agda
is-not-contractible-is-noncontractible :
  {l : Level} {X : UU l} → is-noncontractible X → is-not-contractible X
is-not-contractible-is-noncontractible
  ( pair zero-ℕ H) = is-not-contractible-is-empty H
is-not-contractible-is-noncontractible (pair (succ-ℕ n) (pair x (pair y H))) C =
  is-not-contractible-is-noncontractible (pair n H) (is-prop-is-contr C x y)
```
