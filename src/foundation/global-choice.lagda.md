---
title: Global choice
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation.global-choice where

open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.equivalences using (map-equiv)
open import foundation.functoriality-propositional-truncation using
  ( map-trunc-Prop)
open import foundation.hilberts-epsilon-operators using
  ( ε-operator-Hilbert)
open import foundation.negation using (¬)
open import foundation.propositional-truncations using
  ( type-trunc-Prop; apply-universal-property-trunc-Prop)
open import foundation.universe-levels using (Level; UU; lsuc)

open import univalent-combinatorics.2-element-types using
  ( no-section-type-UU-Fin-Level-two-ℕ)
open import univalent-combinatorics.standard-finite-types using
  ( zero-Fin)
```

## Idea

Global choice is the principle that there is a map from `type-trunc-Prop A` back into `A`, for any type `A`. Here, we say that a type `A` satisfies global choice if there is such a map.

## Definition

### The global choice principle

```agda
Global-Choice : (l : Level) → UU (lsuc l)
Global-Choice l = (A : UU l) → ε-operator-Hilbert A
```

## Properties

### The global choice principle is inconsistent in `agda-unimath`

```agda
abstract
  no-global-choice :
    {l : Level} → ¬ ((X : UU l) → type-trunc-Prop X → X)
  no-global-choice f =
    no-section-type-UU-Fin-Level-two-ℕ
      ( λ X →
        f (pr1 X) (map-trunc-Prop (λ e → map-equiv e (zero-Fin 1)) (pr2 X)))
```
