---
title: Lifting structures
---

```agda
module orthogonal-factorization-systems.lifting-structures where

open import foundation.cartesian-product-types
open import foundation.commuting-squares
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.equality-dependent-pair-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.functions
open import foundation.identity-types
open import foundation.homotopies
open import foundation.truncation-levels
open import foundation.unit-type
open import foundation.universe-levels

open import orthogonal-factorization-systems.extensions-of-maps
open import orthogonal-factorization-systems.lifting-squares
open import orthogonal-factorization-systems.lifts-of-maps
```

## Idea

Given two maps, `f : A → X` and `g : B → Y`,

we say that `f` has a _left lifting structure_ with respect to `g`
and that `g` has a _right lifting structure_ with respect to `f`
if there is a choice of lifting squares for every commuting square

```md
  A ------> B
  |         |
 f|         |g
  |         |
  V         V
  X ------> Y.
```

This is the Curry–Howard interpretation of what is classically called
_lifting properties_. However, these are generally structures on the
maps, and not just properties.

## Definition

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → X) (g : B → Y)
  where

  lifting-structure : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  lifting-structure = (i : X → Y) (h : A → B) (H : coherence-square h f g i) → lifting-square h f g i H

  _⧄_ = lifting-structure -- The symbol doesn't have an input sequence :(
```
