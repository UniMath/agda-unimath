---
title: Weakly constant maps
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation.weakly-constant-maps where

open import foundation.dependent-pair-types using (Σ; pr1; pr2; pair)
open import foundation.identity-types using (_＝_)
open import foundation.propositions using (is-prop; is-prop-Π; UU-Prop)
open import foundation.sets using (UU-Set; type-Set; is-set-type-Set)
open import foundation.universe-levels using (Level; UU; _⊔_)
```

## Idea

A map `f : A → B` is said to be weakly constant if any two elements in `A` are mapped to identical elements in `B`.

## Definition

```agda
is-weakly-constant-map :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} → (A → B) → UU (l1 ⊔ l2)
is-weakly-constant-map {A = A} f = (x y : A) → f x ＝ f y

module _
  {l1 l2 : Level} {A : UU l1} (B : UU-Set l2) (f : A → type-Set B)
  where
  
  abstract
    is-prop-is-weakly-constant-map-Set : is-prop (is-weakly-constant-map f)
    is-prop-is-weakly-constant-map-Set =
      is-prop-Π (λ x → is-prop-Π (λ y → is-set-type-Set B (f x) (f y)))
  
  is-weakly-constant-map-Prop : UU-Prop (l1 ⊔ l2)
  pr1 is-weakly-constant-map-Prop = is-weakly-constant-map f
  pr2 is-weakly-constant-map-Prop = is-prop-is-weakly-constant-map-Set
```
