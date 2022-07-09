---
title: Normal subgroups
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module group-theory.normal-subgroups where

open import foundation.dependent-pair-types
open import foundation.propositions
open import foundation.universe-levels

open import group-theory.conjugation
open import group-theory.groups
open import group-theory.subgroups
```

## Idea

A normal subgroup of `G` is a subgroup `H` of `G` which is closed under conjugation.

## Definition

```agda
is-normal-subgroup-Prop :
  {l1 l2 : Level} (G : Group l1) (H : Subgroup l2 G) → UU-Prop (l1 ⊔ l2)
is-normal-subgroup-Prop G H =
  Π-Prop
    ( type-Group G)
    ( λ g →
      Π-Prop
        ( type-Subgroup G H)
        ( λ h →
          subset-Subgroup G H
            ( conjugation-Group G g (inclusion-Subgroup G H h))))

is-normal-Subgroup :
  {l1 l2 : Level} (G : Group l1) (H : Subgroup l2 G) → UU (l1 ⊔ l2)
is-normal-Subgroup G H = type-Prop (is-normal-subgroup-Prop G H)

is-prop-is-normal-Subgroup :
  {l1 l2 : Level} (G : Group l1) (H : Subgroup l2 G) →
  is-prop (is-normal-Subgroup G H)
is-prop-is-normal-Subgroup G H = is-prop-type-Prop (is-normal-subgroup-Prop G H)

Normal-Subgroup :
  {l1 : Level} (l2 : Level) (G : Group l1) → UU (l1 ⊔ lsuc l2)
Normal-Subgroup l2 G = Σ (Subgroup l2 G) (is-normal-Subgroup G)

module _
  {l1 l2 : Level} (G : Group l1) (N : Normal-Subgroup l2 G)
  where

  subgroup-Normal-Subgroup : Subgroup l2 G
  subgroup-Normal-Subgroup = pr1 N

  is-normal-subgroup-Normal-Subgroup :
    is-normal-Subgroup G subgroup-Normal-Subgroup
  is-normal-subgroup-Normal-Subgroup = pr2 N

  subset-Normal-Subgroup : subset-Group l2 G
  subset-Normal-Subgroup = subset-Subgroup G subgroup-Normal-Subgroup

  type-Normal-Subgroup : UU (l1 ⊔ l2)
  type-Normal-Subgroup = type-Subgroup G subgroup-Normal-Subgroup

  inclusion-Normal-Subgroup : type-Normal-Subgroup → type-Group G
  inclusion-Normal-Subgroup = inclusion-Subgroup G subgroup-Normal-Subgroup

  is-in-Normal-Subgroup : type-Group G → UU l2
  is-in-Normal-Subgroup = is-in-Subgroup G subgroup-Normal-Subgroup

  is-prop-is-in-Normal-Subgroup :
    (g : type-Group G) → is-prop (is-in-Normal-Subgroup g)
  is-prop-is-in-Normal-Subgroup =
    is-prop-is-in-Subgroup G subgroup-Normal-Subgroup

  is-subgroup-Normal-Subgroup :
    is-subgroup-subset-Group G subset-Normal-Subgroup
  is-subgroup-Normal-Subgroup =
    is-subgroup-Subgroup G subgroup-Normal-Subgroup

  contains-unit-Normal-Subgroup : is-in-Normal-Subgroup (unit-Group G)
  contains-unit-Normal-Subgroup =
    contains-unit-Subgroup G subgroup-Normal-Subgroup

  is-closed-under-mul-Normal-Subgroup :
    is-closed-under-mul-subset-Group G subset-Normal-Subgroup
  is-closed-under-mul-Normal-Subgroup =
    is-closed-under-mul-Subgroup G subgroup-Normal-Subgroup

  is-closed-under-inv-Normal-Subgroup :
    is-closed-under-inv-subset-Group G subset-Normal-Subgroup
  is-closed-under-inv-Normal-Subgroup =
    is-closed-under-inv-Subgroup G subgroup-Normal-Subgroup
```
