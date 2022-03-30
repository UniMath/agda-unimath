---
title: 2-element decidable subtypes
---

```agda
{-# OPTIONS --without-K --exact-split --allow-unsolved-metas #-}

module univalent-combinatorics.2-element-decidable-subtypes where

open import elementary-number-theory.natural-numbers using (ℕ)
open import
  elementary-number-theory.well-ordering-principle-standard-finite-types using
  ( well-ordering-principle-∃-Fin)

open import foundation.automorphisms using (Aut)
open import foundation.decidable-equality using
  ( has-decidable-equality; is-set-has-decidable-equality)
open import foundation.decidable-subtypes using
  ( decidable-subtype; type-decidable-subtype; subtype-decidable-subtype;
    is-decidable-subtype; is-decidable-subtype-subtype-decidable-subtype;
    type-prop-decidable-subtype; is-prop-type-prop-decidable-subtype)
open import foundation.decidable-types using (is-decidable; is-decidable-coprod)
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.equivalences using (_≃_)
open import foundation.identity-types using (Id)
open import foundation.negation using (¬)
open import foundation.propositions using (is-prop; eq-is-prop)
open import foundation.subtypes using (subtype)
open import foundation.universe-levels using (Level; UU; _⊔_; lsuc)

open import univalent-combinatorics.2-element-subtypes using
  ( type-prop-standard-2-Element-Subtype;
    is-prop-type-prop-standard-2-Element-Subtype;
    subtype-standard-2-Element-Subtype; type-standard-2-Element-Subtype;
    equiv-type-standard-2-Element-Subtype;
    has-two-elements-type-standard-2-Element-Subtype)
open import univalent-combinatorics.2-element-types using
  ( has-two-elements; 2-Element-Type; swap-2-Element-Type;
    map-swap-2-Element-Type; compute-swap-2-Element-Type)
open import univalent-combinatorics.standard-finite-types using (Fin)
```

## Idea

A 2-element decidable subtype of a type `A` is a decidable subtype of `A` of which the underlying type has 2 elements.

## Definition

### The type of 2-element decidable subtypes

```agda
2-Element-Decidable-Subtype :
  {l1 : Level} (l2 : Level) → UU l1 → UU (l1 ⊔ lsuc l2)
2-Element-Decidable-Subtype l2 X =
  Σ (decidable-subtype l2 X) (λ P → has-two-elements (type-decidable-subtype P))

module _
  {l1 l2 : Level} {X : UU l1} (P : 2-Element-Decidable-Subtype l2 X)
  where
  
  decidable-subtype-2-Element-Decidable-Subtype : decidable-subtype l2 X
  decidable-subtype-2-Element-Decidable-Subtype = pr1 P

  subtype-2-Element-Decidable-Subtype : subtype l2 X
  subtype-2-Element-Decidable-Subtype =
    subtype-decidable-subtype decidable-subtype-2-Element-Decidable-Subtype

  is-decidable-subtype-subtype-2-Element-Decidable-Subtype :
    is-decidable-subtype subtype-2-Element-Decidable-Subtype
  is-decidable-subtype-subtype-2-Element-Decidable-Subtype =
    is-decidable-subtype-subtype-decidable-subtype
      decidable-subtype-2-Element-Decidable-Subtype

  type-prop-2-Element-Decidable-Subtype : X → UU l2
  type-prop-2-Element-Decidable-Subtype =
    type-prop-decidable-subtype decidable-subtype-2-Element-Decidable-Subtype

  is-prop-type-prop-2-Element-Decidable-Subtype :
    (x : X) → is-prop (type-prop-2-Element-Decidable-Subtype x)
  is-prop-type-prop-2-Element-Decidable-Subtype =
    is-prop-type-prop-decidable-subtype
      decidable-subtype-2-Element-Decidable-Subtype

  eq-type-prop-2-Element-Decidable-Subtype :
    {x : X} {y z : type-prop-2-Element-Decidable-Subtype x} → Id y z
  eq-type-prop-2-Element-Decidable-Subtype {x} =
    eq-is-prop (is-prop-type-prop-2-Element-Decidable-Subtype x)
      
  type-2-Element-Decidable-Subtype : UU (l1 ⊔ l2)
  type-2-Element-Decidable-Subtype =
    type-decidable-subtype decidable-subtype-2-Element-Decidable-Subtype

  has-two-elements-type-2-Element-Decidable-Subtype :
    has-two-elements type-2-Element-Decidable-Subtype
  has-two-elements-type-2-Element-Decidable-Subtype = pr2 P

  2-element-type-2-Element-Decidable-Subtype : 2-Element-Type (l1 ⊔ l2)
  pr1 2-element-type-2-Element-Decidable-Subtype =
    type-2-Element-Decidable-Subtype
  pr2 2-element-type-2-Element-Decidable-Subtype =
    has-two-elements-type-2-Element-Decidable-Subtype
```

### The standard 2-element decidable subtypes in a type with decidable equality

```agda
module _
  {l : Level} {X : UU l} (d : has-decidable-equality X) {x y : X}
  (np : ¬ (Id x y))
  where

  type-prop-standard-2-Element-Decidable-Subtype : X → UU l
  type-prop-standard-2-Element-Decidable-Subtype =
    type-prop-standard-2-Element-Subtype
      ( pair X (is-set-has-decidable-equality d))
      ( np)

  is-prop-type-prop-standard-2-Element-Decidable-Subtype :
    (z : X) → is-prop (type-prop-standard-2-Element-Decidable-Subtype z)
  is-prop-type-prop-standard-2-Element-Decidable-Subtype =
    is-prop-type-prop-standard-2-Element-Subtype
      ( pair X (is-set-has-decidable-equality d))
      ( np)

  is-decidable-type-prop-standard-2-Element-Decidable-Subtype :
    (z : X) → is-decidable (type-prop-standard-2-Element-Decidable-Subtype z)
  is-decidable-type-prop-standard-2-Element-Decidable-Subtype z =
    is-decidable-coprod (d x z) (d y z)

  subtype-standard-2-Element-Decidable-Subtype : subtype l X
  subtype-standard-2-Element-Decidable-Subtype =
    subtype-standard-2-Element-Subtype
      ( pair X (is-set-has-decidable-equality d))
      ( np)
      
  decidable-subtype-standard-2-Element-Decidable-Subtype : decidable-subtype l X
  pr1 (decidable-subtype-standard-2-Element-Decidable-Subtype z) =
    type-prop-standard-2-Element-Decidable-Subtype z
  pr1 (pr2 (decidable-subtype-standard-2-Element-Decidable-Subtype z)) =
    is-prop-type-prop-standard-2-Element-Decidable-Subtype z
  pr2 (pr2 (decidable-subtype-standard-2-Element-Decidable-Subtype z)) =
    is-decidable-type-prop-standard-2-Element-Decidable-Subtype z

  type-standard-2-Element-Decidable-Subtype : UU l
  type-standard-2-Element-Decidable-Subtype =
    type-standard-2-Element-Subtype
      ( pair X (is-set-has-decidable-equality d))
      ( np)

  equiv-type-standard-2-Element-Decidable-Subtype :
    Fin 2 ≃ type-standard-2-Element-Decidable-Subtype
  equiv-type-standard-2-Element-Decidable-Subtype =
    equiv-type-standard-2-Element-Subtype
      ( pair X (is-set-has-decidable-equality d))
      ( np)

  has-two-elements-type-standard-2-Element-Decidable-Subtype :
    has-two-elements type-standard-2-Element-Decidable-Subtype
  has-two-elements-type-standard-2-Element-Decidable-Subtype =
    has-two-elements-type-standard-2-Element-Subtype
      ( pair X (is-set-has-decidable-equality d))
      ( np)

  2-element-type-standard-2-Element-Decidable-Subtype : 2-Element-Type l
  pr1 2-element-type-standard-2-Element-Decidable-Subtype =
    type-standard-2-Element-Decidable-Subtype
  pr2 2-element-type-standard-2-Element-Decidable-Subtype =
    has-two-elements-type-standard-2-Element-Decidable-Subtype

  standard-2-Element-Decidable-Subtype : 2-Element-Decidable-Subtype l X
  pr1 standard-2-Element-Decidable-Subtype =
    decidable-subtype-standard-2-Element-Decidable-Subtype
  pr2 standard-2-Element-Decidable-Subtype =
    has-two-elements-type-standard-2-Element-Decidable-Subtype
```

### Swapping the elements in a 2-element subtype

```agda
module _
  {l1 l2 : Level} {X : UU l1} (P : 2-Element-Decidable-Subtype l2 X)
  where

  swap-2-Element-Decidable-Subtype : Aut (type-2-Element-Decidable-Subtype P)
  swap-2-Element-Decidable-Subtype =
    swap-2-Element-Type (2-element-type-2-Element-Decidable-Subtype P)

  map-swap-2-Element-Decidable-Subtype :
    type-2-Element-Decidable-Subtype P → type-2-Element-Decidable-Subtype P
  map-swap-2-Element-Decidable-Subtype =
    map-swap-2-Element-Type (2-element-type-2-Element-Decidable-Subtype P)

  compute-swap-2-Element-Decidable-Subtype :
    (x y : type-2-Element-Decidable-Subtype P) → ¬ (Id x y) →
    Id (map-swap-2-Element-Decidable-Subtype x) y
  compute-swap-2-Element-Decidable-Subtype =
    compute-swap-2-Element-Type (2-element-type-2-Element-Decidable-Subtype P)
```

## Properties

### Any 2-element decidable subtype of a standard finite type is a standard 2-element decidable subtype

```agda
module _
  {l : Level} {n : ℕ} (P : 2-Element-Decidable-Subtype l (Fin n))
  where

  least-element-2-element-subtype-Fin : type-2-Element-Decidable-Subtype P
  least-element-2-element-subtype-Fin =
    {!well-ordering-principle-∃-Fin (decidable-subtype-2-Element-Decidable-Subtype P) ?!}

```
