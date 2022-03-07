# Involutions

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation.involutions where

open import foundation.automorphisms using (Aut)
open import foundation.equivalences using
  ( map-equiv; is-equiv; is-equiv-has-inverse)
open import foundation.functions using (_∘_; id)
open import foundation.homotopies using (_~_)
open import foundation.universe-levels using (Level; UU)
```

## Idea

An involution on a type `A` is a map (or an equivalence) `f : A → A` such that `(f ∘ f) ~ id`

## Definition

```agda
module _
  {l : Level} {A : UU l}
  where

  is-involution : (A → A) → UU l
  is-involution f = (f ∘ f) ~ id

  is-involution-aut : Aut A → UU l
  is-involution-aut e = is-involution (map-equiv e)
```

## Properties

### Any involution is an equivalence

```agda
is-equiv-is-involution :
  {l : Level} {A : UU l} {f : A → A} → is-involution f → is-equiv f
is-equiv-is-involution {f = f} H = is-equiv-has-inverse f H H
```
