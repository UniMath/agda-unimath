---
title: Decidable equivalence relations
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation.decidable-equivalence-relations where

open import foundation.decidable-propositions
open import foundation.decidable-relations
open import foundation.decidable-subtypes
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.equivalence-relations
open import foundation.existential-quantification
open import foundation.identity-types
open import foundation.propositions
open import foundation.subtypes
open import foundation.universe-levels
```

## Idea

A decidable equivalence relation on a type `X` is an equivalence relation `R` on `X` such that `R x y` is a decidable proposition for each `x y : X`.

## Definitions

### Decidable equivalence relations

```agda
Decidable-Equivalence-Relation :
  {l1 : Level} (l2 : Level) → UU l1 → UU (l1 ⊔ lsuc l2)
Decidable-Equivalence-Relation l2 X =
  Σ ( Decidable-Relation l2 X)
    ( λ R → is-equivalence-relation (relation-Decidable-Relation R))

module _
  {l1 l2 : Level} {X : UU l1} (R : Decidable-Equivalence-Relation l2 X)
  where

  decidable-relation-Decidable-Equivalence-Relation :
    Decidable-Relation l2 X
  decidable-relation-Decidable-Equivalence-Relation = pr1 R

  relation-Decidable-Equivalence-Relation : X → X → UU-Prop l2
  relation-Decidable-Equivalence-Relation =
    relation-Decidable-Relation
      decidable-relation-Decidable-Equivalence-Relation

  sim-Decidable-Equivalence-Relation : X → X → UU l2
  sim-Decidable-Equivalence-Relation =
    type-Decidable-Relation decidable-relation-Decidable-Equivalence-Relation

  is-prop-sim-Decidable-Equivalence-Relation :
    (x y : X) → is-prop (sim-Decidable-Equivalence-Relation x y)
  is-prop-sim-Decidable-Equivalence-Relation =
    is-prop-type-Decidable-Relation
      decidable-relation-Decidable-Equivalence-Relation

  is-decidable-sim-Decidable-Equivalence-Relation :
    (x y : X) → is-decidable (sim-Decidable-Equivalence-Relation x y)
  is-decidable-sim-Decidable-Equivalence-Relation =
    is-decidable-type-Decidable-Relation
      decidable-relation-Decidable-Equivalence-Relation

  is-equivalence-relation-Decidable-Equivalence-Relation :
    is-equivalence-relation relation-Decidable-Equivalence-Relation
  is-equivalence-relation-Decidable-Equivalence-Relation = pr2 R

  equivalence-relation-Decidable-Equivalence-Relation : Eq-Rel l2 X
  pr1 equivalence-relation-Decidable-Equivalence-Relation =
    relation-Decidable-Equivalence-Relation
  pr2 equivalence-relation-Decidable-Equivalence-Relation =
    is-equivalence-relation-Decidable-Equivalence-Relation

  refl-Decidable-Equivalence-Relation :
    {x : X} → sim-Decidable-Equivalence-Relation x x
  refl-Decidable-Equivalence-Relation =
    refl-Eq-Rel equivalence-relation-Decidable-Equivalence-Relation

  symmetric-Decidable-Equivalence-Relation :
    {x y : X} → sim-Decidable-Equivalence-Relation x y →
    sim-Decidable-Equivalence-Relation y x
  symmetric-Decidable-Equivalence-Relation =
    symm-Eq-Rel equivalence-relation-Decidable-Equivalence-Relation

  transitive-Decidable-Equivalence-Relation :
    {x y z : X} → sim-Decidable-Equivalence-Relation x y →
    sim-Decidable-Equivalence-Relation y z →
    sim-Decidable-Equivalence-Relation x z
  transitive-Decidable-Equivalence-Relation =
    trans-Eq-Rel equivalence-relation-Decidable-Equivalence-Relation
```

### Equivalence classes of decidable equivalence relations

```agda
module _
  {l1 l2 : Level} {X : UU l1} (R : Decidable-Equivalence-Relation l2 X)
  where

  is-equivalence-class-Decidable-Equivalence-Relation :
    decidable-subtype l2 X → UU (l1 ⊔ lsuc l2)
  is-equivalence-class-Decidable-Equivalence-Relation P =
    ∃ (λ x → Id P (decidable-relation-Decidable-Equivalence-Relation R x))
```
