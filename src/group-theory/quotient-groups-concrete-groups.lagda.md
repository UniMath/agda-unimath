---
title: Quotient groups of concrete groups
---

```agda
module group-theory.quotient-groups-concrete-groups where

open import foundation.0-images-of-maps
open import foundation.dependent-pair-types
open import foundation.fibers-of-maps
open import foundation.set-truncations
open import foundation.sets
open import foundation.universe-levels

open import group-theory.concrete-group-actions
open import group-theory.concrete-groups
open import group-theory.mere-equivalences-concrete-group-actions
open import group-theory.normal-subgroups-concrete-groups

open import structured-types.pointed-types
```

## Idea

Given a normal subgroup `N` of a concrete group `G`, the quotient group `G/N` is a concrete group that satisfies the universal property that for any concrete group homomorphism `f : G → H` such that the kernel of `f` is contained in `N`, then `f` extends uniquely to a group homomorphism `G/N → H`.

The quotient `G/N` can be constructed in several ways.

1. We can construct `G/N` as the type of `G`-sets merely equivalent to the coset action of `N`. Since this construction is reminiscent of the torsor construction of BG, we call this the **transitive construction** of `G/N`.
2. We can construct `G/N` as the 0-image of the coset action `N : BG → U`. We call this the **0-image construction** of `G/N`. 

## Definitions

### The transitive construction of `G/N`

```agda
module _
  { l1 l2 : Level} (G : Concrete-Group l1)
  ( N : normal-subgroup-Concrete-Group l2 G)
  where

  classifying-type-transitive-quotient-Concrete-Group : UU (l1 ⊔ lsuc l2)
  classifying-type-transitive-quotient-Concrete-Group =
    Σ ( action-Concrete-Group l2 G)
      ( mere-equiv-action-Concrete-Group G
        ( action-normal-subgroup-Concrete-Group G N))

  shape-transitive-quotient-Concrete-Group :
    classifying-type-transitive-quotient-Concrete-Group
  pr1 shape-transitive-quotient-Concrete-Group =
    action-normal-subgroup-Concrete-Group G N
  pr2 shape-transitive-quotient-Concrete-Group =
    refl-mere-equiv-action-Concrete-Group G
      ( action-normal-subgroup-Concrete-Group G N)

  classifying-pointed-type-transitive-quotient-Concrete-Group :
    Pointed-Type (l1 ⊔ lsuc l2)
  pr1 classifying-pointed-type-transitive-quotient-Concrete-Group =
    classifying-type-transitive-quotient-Concrete-Group
  pr2 classifying-pointed-type-transitive-quotient-Concrete-Group =
    shape-transitive-quotient-Concrete-Group
```

### The 0-image construction of `G/N`

```agda
module _
  { l1 l2 : Level} (G : Concrete-Group l1)
  ( N : normal-subgroup-Concrete-Group l2 G)
  where

  classifying-type-0-image-quotient-Concrete-Group : UU (l1 ⊔ lsuc l2)
  classifying-type-0-image-quotient-Concrete-Group =
    0-im (action-normal-subgroup-Concrete-Group G N)

  shape-0-image-quotient-Concrete-Group :
    classifying-type-0-image-quotient-Concrete-Group
  shape-0-image-quotient-Concrete-Group =
    unit-0-im
      ( action-normal-subgroup-Concrete-Group G N)
      ( shape-Concrete-Group G)

  classifying-pointed-type-0-image-quotient-Concrete-Group :
    Pointed-Type (l1 ⊔ lsuc l2)
  pr1 classifying-pointed-type-0-image-quotient-Concrete-Group =
    classifying-type-0-image-quotient-Concrete-Group
  pr2 classifying-pointed-type-0-image-quotient-Concrete-Group =
    shape-0-image-quotient-Concrete-Group
```
