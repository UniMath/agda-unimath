---
title: Transitive concrete group actions
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module group-theory.transitive-concrete-group-actions where

open import foundation.connected-types
open import foundation.dependent-pair-types
open import foundation.propositions
open import foundation.sets
open import foundation.universe-levels

open import group-theory.concrete-group-actions
open import group-theory.concrete-groups
open import group-theory.orbits-concrete-group-actions
```

## Definition

```agda
is-transitive-action-Concrete-Group-Prop :
  {l1 l2 : Level} (G : Concrete-Group l1) → action-Concrete-Group l2 G →
  UU-Prop (l1 ⊔ l2)
is-transitive-action-Concrete-Group-Prop G X =
  is-path-connected-Prop (orbit-action-Concrete-Group G X)

is-transitive-action-Concrete-Group :
  {l1 l2 : Level} (G : Concrete-Group l1) → action-Concrete-Group l2 G →
  UU (l1 ⊔ l2)
is-transitive-action-Concrete-Group G X =
  type-Prop (is-transitive-action-Concrete-Group-Prop G X)

is-prop-is-transitive-action-Concrete-Group :
  {l1 l2 : Level} (G : Concrete-Group l1) (X : action-Concrete-Group l2 G) →
  is-prop (is-transitive-action-Concrete-Group G X)
is-prop-is-transitive-action-Concrete-Group G X =
  is-prop-type-Prop (is-transitive-action-Concrete-Group-Prop G X)

transitive-action-Concrete-Group :
  {l1 : Level} (l2 : Level) (G : Concrete-Group l1) → UU (l1 ⊔ lsuc l2)
transitive-action-Concrete-Group l2 G =
  Σ (action-Concrete-Group l2 G) (is-transitive-action-Concrete-Group G)

module _
  {l1 l2 : Level} (G : Concrete-Group l1)
  (X : transitive-action-Concrete-Group l2 G)
  where

  action-transitive-action-Concrete-Group :
    action-Concrete-Group l2 G
  action-transitive-action-Concrete-Group = pr1 X

  is-transitive-transitive-action-Concrete-Group :
    is-transitive-action-Concrete-Group G
      action-transitive-action-Concrete-Group
  is-transitive-transitive-action-Concrete-Group = pr2 X
```
