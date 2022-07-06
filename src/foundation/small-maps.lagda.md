---
title: Small maps
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation.small-maps where

open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.fibers-of-maps using (fib)
open import foundation.locally-small-types using (is-locally-small-is-small)
open import foundation.propositions using (is-prop; is-prop-Π; UU-Prop)
open import foundation.small-types using
  ( is-small; is-small-Σ; is-prop-is-small)
open import foundation.universe-levels using (Level; UU; _⊔_; lsuc)
```

## Idea

A map is said to be small if its fibers are small.

## Definition

```agda
is-small-map :
  (l : Level) {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  (A → B) → UU (lsuc l ⊔ (l1 ⊔ l2))
is-small-map l {B = B} f = (b : B) → is-small l (fib f b)
```

## Properties

### Any map between small types is small

```agda
abstract
  is-small-fib :
    (l : Level) {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
    is-small l A → is-small l B → (b : B) → is-small l (fib f b)
  is-small-fib l f H K b =
    is-small-Σ l H (λ a → is-locally-small-is-small l K (f a) b)
```

### Being a small map is a property

```agda
abstract
  is-prop-is-small-map :
    (l : Level) {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
    is-prop (is-small-map l f)
  is-prop-is-small-map l f =
    is-prop-Π (λ x → is-prop-is-small l (fib f x))

is-small-map-Prop :
  (l : Level) {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  UU-Prop (lsuc l ⊔ l1 ⊔ l2)
pr1 (is-small-map-Prop l f) = is-small-map l f
pr2 (is-small-map-Prop l f) = is-prop-is-small-map l f
```
