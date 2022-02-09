# Conjunction of propositions

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation.conjunction where

open import foundation.dependent-pair-types using (pr1; pr2; pair)
open import foundation.propositions using
  ( prod-Prop; UU-Prop; type-Prop; is-prop; is-prop-type-Prop)
open import foundation.universe-levels using (Level; UU; _⊔_)
```

## Idea

The conjunction of two propositions `P` and `Q` is the proposition that both `P` and `Q` hold.

## Definition

```agda
conj-Prop = prod-Prop

type-conj-Prop :
  {l1 l2 : Level} → UU-Prop l1 → UU-Prop l2 → UU (l1 ⊔ l2)
type-conj-Prop P Q = type-Prop (conj-Prop P Q)

abstract
  is-prop-type-conj-Prop :
    {l1 l2 : Level} (P : UU-Prop l1) (Q : UU-Prop l2) →
    is-prop (type-conj-Prop P Q)
  is-prop-type-conj-Prop P Q = is-prop-type-Prop (conj-Prop P Q)
```

## Properties

### Introduction rule for conjunction

```
intro-conj-Prop :
  {l1 l2 : Level} (P : UU-Prop l1) (Q : UU-Prop l2) →
  type-Prop P → type-Prop Q → type-conj-Prop P Q
pr1 (intro-conj-Prop P Q p q) = p
pr2 (intro-conj-Prop P Q p q) = q
```
