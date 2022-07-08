---
title: Involutions
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation.involutions where

open import foundation.automorphisms using (Aut)
open import foundation.dependent-pair-types
open import foundation.equivalences using
  ( map-equiv; is-equiv; is-equiv-has-inverse; inv-equiv; eq-htpy-equiv;
    htpy-eq-equiv; right-inverse-law-equiv)
open import foundation.functions using (_∘_; id)
open import foundation.homotopies using (_~_; refl-htpy)
open import foundation.identity-types using (_＝_; refl; _∙_; inv)
open import foundation.injective-maps using (is-injective-map-equiv)
open import foundation.universe-levels using (Level; UU)
```

## Idea

An involution on a type `A` is a map (or an equivalence) `f : A → A` such that `(f ∘ f) ~ id`

## Definition

### The condition that a map is an involution

```agda
module _
  {l : Level} {A : UU l}
  where

  is-involution : (A → A) → UU l
  is-involution f = (f ∘ f) ~ id

  is-involution-aut : Aut A → UU l
  is-involution-aut e = is-involution (map-equiv e)
```

### The type of involutions on `X`

```agda
involution : {l : Level} → UU l → UU l
involution A = Σ (A → A) is-involution

module _
  {l : Level} {A : UU l} (f : involution A)
  where

  map-involution : A → A
  map-involution = pr1 f

  is-involution-map-involution : is-involution map-involution
  is-involution-map-involution = pr2 f
```

## Properties

### Any involution is an equivalence

```agda
is-equiv-is-involution :
  {l : Level} {A : UU l} {f : A → A} → is-involution f → is-equiv f
is-equiv-is-involution {f = f} H = is-equiv-has-inverse f H H
```

### Involutions are their own inverse

```agda
own-inverse-is-involution :
  {l : Level} {A : UU l} {f : Aut A} → is-involution-aut f → inv-equiv f ＝ f
own-inverse-is-involution {f = f} p =
  eq-htpy-equiv
    (λ x →
      is-injective-map-equiv
        ( f)
        ( ( htpy-eq-equiv (right-inverse-law-equiv f) x) ∙
          ( inv (p x))))
```
