# Global choice

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation.global-choice where

open import foundation.equivalences using (_≃_; map-equiv; map-inv-equiv)
open import foundation.functions using (_∘_)
open import foundation.functoriality-propositional-truncation using
  ( functor-trunc-Prop)
open import foundation.propositional-truncations using
  ( type-trunc-Prop)
open import foundation.universe-levels using (Level; UU; lsuc)
```

## Idea

Global choice is the principle that there is a map from `type-trunc-Prop A` back into `A`, for any type `A`. Here, we say that a type `A` satisfies global choice if there is such a map.

## Definition

```agda
global-choice : {l : Level} → UU l → UU l
global-choice X = type-trunc-Prop X → X

Global-Choice : (l : Level) → UU (lsuc l)
Global-Choice l = (A : UU l) → global-choice A

global-choice-equiv :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : X ≃ Y) →
  global-choice X → global-choice Y
global-choice-equiv e f =
  (map-equiv e ∘ f) ∘ (functor-trunc-Prop (map-inv-equiv e))

global-choice-equiv' :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : X ≃ Y) →
  global-choice Y → global-choice X
global-choice-equiv' e f =
  (map-inv-equiv e ∘ f) ∘ (functor-trunc-Prop (map-equiv e))
```
