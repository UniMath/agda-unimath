# Codiscrete maps

```agda
{-# OPTIONS --cohesion --flat-split --rewriting #-}

module modal-type-theory.codiscrete-maps where

open import modal-type-theory.sharp-modality
open import modal-type-theory.codiscrete-types

open import foundation.fibers-of-maps
open import foundation.universe-levels
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.unit-type
open import foundation.empty-types
open import foundation.homotopies
open import foundation.retractions
open import foundation.sections
open import foundation.equivalences
```

## Idea

A map is said to be **codiscrete** if its fibers are codiscrete.

## Definition

```agda
is-codiscrete-map :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} → (A → B) → UU (l1 ⊔ l2)
is-codiscrete-map f = is-codiscrete-family (fib f)
```

## Properties

### Being codiscrete is a property

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  where

  is-codiscrete-map-Prop : Prop (l1 ⊔ l2)
  is-codiscrete-map-Prop = is-codiscrete-family-Prop (fib f)

  is-property-is-codiscrete-map : is-prop (is-codiscrete-map f)
  is-property-is-codiscrete-map = is-prop-type-Prop is-codiscrete-map-Prop
```
