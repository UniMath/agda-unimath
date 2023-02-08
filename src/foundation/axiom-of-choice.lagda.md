---
title: The axiom of choice
---

```agda
module foundation.axiom-of-choice where

open import elementary-number-theory.natural-numbers

open import foundation.connected-types
open import foundation.fibers-of-maps
open import foundation.functoriality-propositional-truncation
open import foundation.projective-types
open import foundation.propositional-truncations
open import foundation.sections
open import foundation.sets
open import foundation.truncated-types
open import foundation.truncation-levels
open import foundation.universe-levels
```

## Idea

The axiom of choice asserts that for every family of inhabited types indexed by a set, the type of sections of that family is inhabited.

## Definition

### The axiom of choice restricted to sets

```agda
AC-Set : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
AC-Set l1 l2 =
  (A : Set l1) (B : type-Set A → Set l2) →
  ((x : type-Set A) → type-trunc-Prop (type-Set (B x))) →
  type-trunc-Prop ((x : type-Set A) → type-Set (B x))
```

### The axiom of choice

```agda
AC-0 : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
AC-0 l1 l2 =
  (A : Set l1) (B : type-Set A → UU l2) →
  ((x : type-Set A) → type-trunc-Prop (B x)) →
  type-trunc-Prop ((x : type-Set A) → B x)
```

## Properties

### Every type is set-projective if and only if the axiom of choice holds

```agda
is-set-projective-AC-0 :
  {l1 l2 l3 : Level} → AC-0 l2 (l1 ⊔ l2) → (X : UU l3) → is-set-projective l1 l2 X
is-set-projective-AC-0 ac X A B f h =
  map-trunc-Prop {!!} (ac B (fib f) {!!})
```
