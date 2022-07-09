---
title: Disjunction of propositions
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation.disjunction where

open import foundation.conjunction using (conj-Prop)
open import foundation.coproduct-types using (_+_; inl; inr; ind-coprod)
open import foundation.decidable-propositions using
  (decidable-Prop; prop-decidable-Prop; type-decidable-Prop; is-decidable-type-decidable-Prop)
open import foundation.decidable-types using
  (is-decidable-coprod; is-decidable-trunc-Prop-is-merely-decidable)
open import foundation.dependent-pair-types using (pr1; pr2; pair)
open import foundation.equivalences using (is-equiv)
open import foundation.functions using (_∘_)
open import foundation.propositional-truncations using
  ( trunc-Prop; unit-trunc-Prop; map-universal-property-trunc-Prop)
open import foundation.propositions using
  ( UU-Prop; type-Prop; is-prop; is-prop-type-Prop; type-hom-Prop; hom-Prop;
    is-equiv-is-prop)
open import foundation.universe-levels using (Level; UU; _⊔_)
```

## Idea

The disjunction of two propositions `P` and `Q` is the proposition that `P` holds or `Q` holds.

## Definition

```agda
disj-Prop :
  {l1 l2 : Level} → UU-Prop l1 → UU-Prop l2 → UU-Prop (l1 ⊔ l2)
disj-Prop P Q = trunc-Prop (type-Prop P + type-Prop Q)

type-disj-Prop :
  {l1 l2 : Level} → UU-Prop l1 → UU-Prop l2 → UU (l1 ⊔ l2)
type-disj-Prop P Q = type-Prop (disj-Prop P Q)

abstract
  is-prop-type-disj-Prop :
    {l1 l2 : Level} (P : UU-Prop l1) (Q : UU-Prop l2) →
    is-prop (type-disj-Prop P Q)
  is-prop-type-disj-Prop P Q = is-prop-type-Prop (disj-Prop P Q)

disj-decidable-Prop : 
  {l1 l2 : Level} → decidable-Prop l1 → decidable-Prop l2 → decidable-Prop (l1 ⊔ l2)
pr1 (disj-decidable-Prop P Q) = type-disj-Prop (prop-decidable-Prop P) (prop-decidable-Prop Q)
pr1 (pr2 (disj-decidable-Prop P Q)) =
  is-prop-type-disj-Prop (prop-decidable-Prop P) (prop-decidable-Prop Q)
pr2 (pr2 (disj-decidable-Prop P Q)) =
  is-decidable-trunc-Prop-is-merely-decidable
    ( type-decidable-Prop P + type-decidable-Prop Q)
    ( unit-trunc-Prop
      ( is-decidable-coprod
        ( is-decidable-type-decidable-Prop P)
        ( is-decidable-type-decidable-Prop Q)))
```

## Properties

### The introduction rules for disjunction

```agda
inl-disj-Prop :
  {l1 l2 : Level} (P : UU-Prop l1) (Q : UU-Prop l2) →
  type-hom-Prop P (disj-Prop P Q)
inl-disj-Prop P Q = unit-trunc-Prop ∘ inl

inr-disj-Prop :
  {l1 l2 : Level} (P : UU-Prop l1) (Q : UU-Prop l2) →
  type-hom-Prop Q (disj-Prop P Q)
inr-disj-Prop P Q = unit-trunc-Prop ∘ inr
```

### The elimination rule and universal property of disjunction

```agda
ev-disj-Prop :
  {l1 l2 l3 : Level} (P : UU-Prop l1) (Q : UU-Prop l2) (R : UU-Prop l3) →
  type-hom-Prop
    ( hom-Prop (disj-Prop P Q) R)
    ( conj-Prop (hom-Prop P R) (hom-Prop Q R))
pr1 (ev-disj-Prop P Q R h) = h ∘ (inl-disj-Prop P Q)
pr2 (ev-disj-Prop P Q R h) = h ∘ (inr-disj-Prop P Q)

elim-disj-Prop :
  {l1 l2 l3 : Level} (P : UU-Prop l1) (Q : UU-Prop l2) (R : UU-Prop l3) →
  type-hom-Prop
    ( conj-Prop (hom-Prop P R) (hom-Prop Q R))
    ( hom-Prop (disj-Prop P Q) R)
elim-disj-Prop P Q R (pair f g) =
  map-universal-property-trunc-Prop R (ind-coprod (λ t → type-Prop R) f g)

abstract
  is-equiv-ev-disj-Prop :
    {l1 l2 l3 : Level} (P : UU-Prop l1) (Q : UU-Prop l2) (R : UU-Prop l3) →
    is-equiv (ev-disj-Prop P Q R)
  is-equiv-ev-disj-Prop P Q R =
    is-equiv-is-prop
      ( is-prop-type-Prop (hom-Prop (disj-Prop P Q) R))
      ( is-prop-type-Prop (conj-Prop (hom-Prop P R) (hom-Prop Q R)))
      ( elim-disj-Prop P Q R)
```
