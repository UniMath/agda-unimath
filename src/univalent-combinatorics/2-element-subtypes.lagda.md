---
title: 2-element subtypes
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module univalent-combinatorics.2-element-subtypes where

open import foundation.coproduct-types using (coprod; inl; inr)
open import foundation.decidable-types using (is-decidable)
open import foundation.decidable-propositions using
  ( decidable-Prop; is-decidable-type-decidable-Prop;
    is-prop-type-decidable-Prop; type-decidable-Prop)
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.equivalences using (_≃_)
open import foundation.identity-types using (Id)
open import foundation.propositions using (type-Prop)
open import foundation.subtypes using (subtype; type-subtype)
open import foundation.unit-type using (star)
open import foundation.universe-levels using (Level; UU; lzero; lsuc; _⊔_)

open import univalent-combinatorics.2-element-types using
  ( has-two-elements; 2-Element-Type)
```

## Idea

A 2-element subtype of a type `A` is a subtype `P` of `A` of which its underlying type `Σ A P` has cardinality 2. Such a subtype is said to be decidable if the proposition `P x` is decidable for every `x : A`.

## Definitions

```agda
2-Element-Subtype : {l1 : Level} (l2 : Level) → UU l1 → UU (l1 ⊔ lsuc l2)
2-Element-Subtype l2 X =
  Σ (subtype l2 X) (λ P → has-two-elements (type-subtype P))

module _
  {l1 l2 : Level} {X : UU l1} (P : 2-Element-Subtype l2 X)
  where
  
  subtype-2-Element-Subtype : subtype l2 X
  subtype-2-Element-Subtype = pr1 P

  type-2-Element-Subtype : UU (l1 ⊔ l2)
  type-2-Element-Subtype = type-subtype subtype-2-Element-Subtype

  has-two-elements-type-2-Element-Subtype :
    has-two-elements type-2-Element-Subtype
  has-two-elements-type-2-Element-Subtype = pr2 P

  2-element-type-2-Element-Subtype : 2-Element-Type (l1 ⊔ l2)
  pr1 2-element-type-2-Element-Subtype = type-2-Element-Subtype
  pr2 2-element-type-2-Element-Subtype = has-two-elements-type-2-Element-Subtype
```
