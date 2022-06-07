# The law of excluded middle

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation.law-of-excluded-middle where

open import foundation.decidable-propositions using (decidable-Prop)
open import foundation.decidable-types using (is-decidable)
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.negation using (¬)
open import foundation.propositions using (UU-Prop; type-Prop; is-prop-type-Prop)
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

### Given LEM, we obtain a map from the type of propositions to the type of all propositions

```agda
decidable-prop-Prop :
  {l : Level} → LEM l → UU-Prop l → decidable-Prop l
pr1 (decidable-prop-Prop lem P) = type-Prop P
pr1 (pr2 (decidable-prop-Prop lem P)) = is-prop-type-Prop P
pr2 (pr2 (decidable-prop-Prop lem P)) = lem P
```

### The unrestricted law of excluded middle does not hold

```agda
abstract
  no-global-decidability :
    {l : Level} → ¬ ((X : UU l) → is-decidable X)
  no-global-decidability {l} d =
    is-not-decidable-type-UU-Fin-Level-two-ℕ (λ X → d (pr1 X))
```
