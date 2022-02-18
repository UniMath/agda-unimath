# The law of excluded middle

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation.law-of-excluded-middle where

open import foundation.decidable-types using (is-decidable)
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.negation using (¬)
open import foundation.propositions using (UU-Prop; type-Prop)
open import foundation.universe-levels using (Level; UU; lsuc)

open import univalent-combinatorics.2-element-types using
  ( is-not-decidable-type-UU-Fin-Level-two-ℕ)
```

## Idea

The law of excluded middle asserts that any proposition `P` is decidable.

## Definition

```agda
LEM : (l : Level) → UU (lsuc l)
LEM l = (P : UU-Prop l) → is-decidable (type-Prop P)
```

## Properties

### The unrestricted law of excluded middle does not hold

```agda
abstract
  no-global-decidability :
    {l : Level} → ¬ ((X : UU l) → is-decidable X)
  no-global-decidability {l} d =
    is-not-decidable-type-UU-Fin-Level-two-ℕ (λ X → d (pr1 X))
```
