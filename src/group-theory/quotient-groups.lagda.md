---
title: Quotient groups
---

```agda
module group-theory.quotient-groups where

open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.identity-types
open import foundation.propositions
open import foundation.subtypes
open import foundation.universe-levels

open import group-theory.groups
open import group-theory.homomorphisms-groups
open import group-theory.kernels
open import group-theory.normal-subgroups
```

## Idea

Given a normal subgroup `H` of `G`, the quotient group `q : G → G/H` such that `H ⊆ ker q`, and such that `q` satisfies the universal group with the property that any group homomorphism `f : G → K` such that `H ⊆ ker f` extends uniquely along `q` to a group homomorphism `G/H → K`.

## Definitions

### Group homomorphisms that nullify a normal subgroup, i.e., that contain a normal subgroup in their kernel

```agda
module _
  {l1 l2 l3 : Level} (G : Group l1) (K : Group l2)
  where
  
  nullifies-normal-subgroup-hom-Group-Prop :
    type-hom-Group G K → Normal-Subgroup l3 G → Prop (l1 ⊔ l2 ⊔ l3)
  nullifies-normal-subgroup-hom-Group-Prop f H =
    contains-Normal-Subgroup-Prop G H (kernel-hom-Group G K f)

  nullifies-normal-subgroup-hom-Group :
    type-hom-Group G K → Normal-Subgroup l3 G → UU (l1 ⊔ l2 ⊔ l3)
  nullifies-normal-subgroup-hom-Group f H =
    type-Prop (nullifies-normal-subgroup-hom-Group-Prop f H)

  nullifying-hom-Group : Normal-Subgroup l3 G → UU (l1 ⊔ l2 ⊔ l3)
  nullifying-hom-Group H =
    type-subtype (λ f → nullifies-normal-subgroup-hom-Group-Prop f H)

  hom-nullifying-hom-Group :
    (H : Normal-Subgroup l3 G) → nullifying-hom-Group H → type-hom-Group G K
  hom-nullifying-hom-Group H = pr1

  nullifies-nullifying-hom-Group :
    (H : Normal-Subgroup l3 G) (f : nullifying-hom-Group H) →
    nullifies-normal-subgroup-hom-Group (hom-nullifying-hom-Group H f) H
  nullifies-nullifying-hom-Group H = pr2
```

### The universal property of quotient groups

```agda
precomp-nullifying-hom-Group :
  {l1 l2 l3 l4 : Level} (G : Group l1) (H : Normal-Subgroup l2 G)
  (K : Group l3) (f : nullifying-hom-Group G K H)
  (L : Group l4) → type-hom-Group K L → nullifying-hom-Group G L H
pr1 (precomp-nullifying-hom-Group G H K f L g) =
  comp-hom-Group G K L g (hom-nullifying-hom-Group G K H f)
pr2 (precomp-nullifying-hom-Group G H K f L g) h p =
  ( ap (map-hom-Group K L g) (nullifies-nullifying-hom-Group G K H f h p)) ∙
  ( preserves-unit-hom-Group K L g)

universal-property-quotient-Group :
  {l1 l2 l3 : Level} (l : Level) (G : Group l1) (H : Normal-Subgroup l2 G)
  (Q : Group l3) (q : nullifying-hom-Group G Q H) → UU (l1 ⊔ l2 ⊔ l3 ⊔ lsuc l)
universal-property-quotient-Group l G H Q q =
  (K : Group l) → is-equiv (precomp-nullifying-hom-Group G H Q q K)
```
