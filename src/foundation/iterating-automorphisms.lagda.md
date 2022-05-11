---
title: Iterating automorphisms
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation.iterating-automorphisms where

open import elementary-number-theory.natural-numbers

open import foundation.automorphisms
open import foundation.equivalences
open import foundation.homotopies
open import foundation.identity-types
open import foundation.iterating-functions
open import foundation.universe-levels
```

## Definition

### Iterating automorphisms

#### Iterating by postcomposition

```agda
module _
  {l : Level} {X : UU l}
  where

  iterate-automorphism : ℕ → Aut X → Aut X
  iterate-automorphism zero-ℕ e = id-equiv
  iterate-automorphism (succ-ℕ n) e = e ∘e (iterate-automorphism n e)

  map-iterate-automorphism : ℕ → Aut X → X → X
  map-iterate-automorphism n e = map-equiv (iterate-automorphism n e)

  is-equiv-map-iterate-automorphism :
    (n : ℕ) (e : Aut X) → is-equiv (map-iterate-automorphism n e)
  is-equiv-map-iterate-automorphism n e =
    is-equiv-map-equiv (iterate-automorphism n e)

  compute-map-iterate-automorphism :
    (n : ℕ) (e : Aut X) → map-iterate-automorphism n e ~ iterate n (map-equiv e)
  compute-map-iterate-automorphism zero-ℕ e = refl-htpy
  compute-map-iterate-automorphism (succ-ℕ n) e =
    map-equiv e ·l (compute-map-iterate-automorphism n e)
```

#### Iterating my precomposition

```agda
module _
  {l : Level} {X : UU l}
  where

  iterate-automorphism' : ℕ → Aut X → Aut X
  iterate-automorphism' zero-ℕ e = id-equiv
  iterate-automorphism' (succ-ℕ n) e = iterate-automorphism' n e ∘e e

  map-iterate-automorphism' : ℕ → Aut X → X → X
  map-iterate-automorphism' n e = map-equiv (iterate-automorphism' n e)

  is-equiv-map-iterate-automorphism' :
    (n : ℕ) (e : Aut X) → is-equiv (map-iterate-automorphism' n e)
  is-equiv-map-iterate-automorphism' n e =
    is-equiv-map-equiv (iterate-automorphism' n e)

  compute-map-iterate-automorphism' :
    (n : ℕ) (e : Aut X) →
    map-iterate-automorphism' n e ~ iterate' n (map-equiv e)
  compute-map-iterate-automorphism' zero-ℕ e = refl-htpy
  compute-map-iterate-automorphism' (succ-ℕ n) e =
    (compute-map-iterate-automorphism' n e ·r (map-equiv e))
```

## Properties

### Iterating by postcomposition is homotopic to iterating by precomposition

```agda
module _
  {l : Level} {X : UU l}
  where

  iterate-automorphism-succ-ℕ :
    (n : ℕ) (e : Aut X) →
    htpy-equiv
      ( iterate-automorphism (succ-ℕ n) e)
      ( iterate-automorphism n e ∘e e)
  iterate-automorphism-succ-ℕ zero-ℕ e = refl-htpy
  iterate-automorphism-succ-ℕ (succ-ℕ n) e =
    map-equiv e ·l (iterate-automorphism-succ-ℕ n e)

  reassociate-iterate-automorphism :
    (n : ℕ) (e : Aut X) →
    htpy-equiv (iterate-automorphism n e) (iterate-automorphism' n e)
  reassociate-iterate-automorphism zero-ℕ e = refl-htpy
  reassociate-iterate-automorphism (succ-ℕ n) e =
    ( iterate-automorphism-succ-ℕ n e) ∙h
    ( reassociate-iterate-automorphism n e ·r map-equiv e)
```
