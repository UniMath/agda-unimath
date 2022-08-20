---
title: Normal subgroups
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module group-theory.normal-subgroups where

open import foundation.binary-relations
open import foundation.dependent-pair-types
open import foundation.equivalence-relations
open import foundation.equivalences
open import foundation.embeddings
open import foundation.fibers-of-maps
open import foundation.functions
open import foundation.identity-types
open import foundation.propositional-maps
open import foundation.propositions
open import foundation.universe-levels

open import group-theory.congruence-relations-groups
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

is-normal-Subgroup' :
  {l1 l2 : Level} (G : Group l1) (H : Subgroup l2 G) → UU (l1 ⊔ l2)
is-normal-Subgroup' G H =
  (x : type-Group G) (y : type-Subgroup G H) →
  is-in-Subgroup G H (conjugation-Group' G x (inclusion-Subgroup G H y))

is-normal-is-normal-Subgroup :
  {l1 l2 : Level} (G : Group l1) (H : Subgroup l2 G) →
  is-normal-Subgroup G H → is-normal-Subgroup' G H
is-normal-is-normal-Subgroup G H K x y =
  tr
    ( is-in-Subgroup G H)
    ( inv (htpy-conjugation-Group G x (inclusion-Subgroup G H y)))
    ( K (inv-Group G x) y)

is-normal-is-normal-Subgroup' :
  {l1 l2 : Level} (G : Group l1) (H : Subgroup l2 G) →
  is-normal-Subgroup' G H → is-normal-Subgroup G H
is-normal-is-normal-Subgroup' G H  K x y =
  tr
    ( is-in-Subgroup G H)
    ( inv (htpy-conjugation-Group' G x (inclusion-Subgroup G H y)))
    ( K (inv-Group G x) y)

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

  is-normal-subgroup-Normal-Subgroup' :
    is-normal-Subgroup' G subgroup-Normal-Subgroup
  is-normal-subgroup-Normal-Subgroup' =
    is-normal-is-normal-Subgroup G
      subgroup-Normal-Subgroup
      is-normal-subgroup-Normal-Subgroup

  subset-Normal-Subgroup : subset-Group l2 G
  subset-Normal-Subgroup = subset-Subgroup G subgroup-Normal-Subgroup

  type-Normal-Subgroup : UU (l1 ⊔ l2)
  type-Normal-Subgroup = type-Subgroup G subgroup-Normal-Subgroup

  inclusion-Normal-Subgroup : type-Normal-Subgroup → type-Group G
  inclusion-Normal-Subgroup = inclusion-Subgroup G subgroup-Normal-Subgroup

  is-emb-inclusion-Normal-Subgroup : is-emb inclusion-Normal-Subgroup
  is-emb-inclusion-Normal-Subgroup =
    is-emb-inclusion-Subgroup G subgroup-Normal-Subgroup

  emb-inclusion-Normal-Subgroup : type-Normal-Subgroup ↪ type-Group G
  emb-inclusion-Normal-Subgroup =
    emb-inclusion-Subgroup G subgroup-Normal-Subgroup

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

  unit-Normal-Subgroup : type-Normal-Subgroup
  unit-Normal-Subgroup = unit-Subgroup G subgroup-Normal-Subgroup

  is-closed-under-mul-Normal-Subgroup :
    is-closed-under-mul-subset-Group G subset-Normal-Subgroup
  is-closed-under-mul-Normal-Subgroup =
    is-closed-under-mul-Subgroup G subgroup-Normal-Subgroup

  mul-Normal-Subgroup :
    type-Normal-Subgroup → type-Normal-Subgroup → type-Normal-Subgroup
  mul-Normal-Subgroup = mul-Subgroup G subgroup-Normal-Subgroup

  is-closed-under-inv-Normal-Subgroup :
    is-closed-under-inv-subset-Group G subset-Normal-Subgroup
  is-closed-under-inv-Normal-Subgroup =
    is-closed-under-inv-Subgroup G subgroup-Normal-Subgroup

  inv-Normal-Subgroup : type-Normal-Subgroup → type-Normal-Subgroup
  inv-Normal-Subgroup = inv-Subgroup G subgroup-Normal-Subgroup

  group-Normal-Subgroup : Group (l1 ⊔ l2)
  group-Normal-Subgroup = group-Subgroup G subgroup-Normal-Subgroup

  conjugation-Normal-Subgroup :
    type-Group G → type-Normal-Subgroup → type-Normal-Subgroup
  pr1 (conjugation-Normal-Subgroup y u) =
    conjugation-Group G y (inclusion-Normal-Subgroup u)
  pr2 (conjugation-Normal-Subgroup y u) =
    is-normal-subgroup-Normal-Subgroup y u

  conjugation-Normal-Subgroup' :
    type-Group G → type-Normal-Subgroup → type-Normal-Subgroup
  pr1 (conjugation-Normal-Subgroup' y u) =
    conjugation-Group' G y (inclusion-Normal-Subgroup u)
  pr2 (conjugation-Normal-Subgroup' y u) =
    is-normal-subgroup-Normal-Subgroup' y u
```

## Properties

### Normal subgroups are in 1-1 correspondence with congruence relations on groups

```agda
module _
  {l1 l2 : Level} (G : Group l1) (N : Normal-Subgroup l2 G)
  where
  
  sim-congruence-Normal-Subgroup : (x y : type-Group G) → UU (l1 ⊔ l2)
  sim-congruence-Normal-Subgroup =
    right-sim-Subgroup G (subgroup-Normal-Subgroup G N)

  is-prop-sim-congruence-Normal-Subgroup :
    (x y : type-Group G) → is-prop (sim-congruence-Normal-Subgroup x y)
  is-prop-sim-congruence-Normal-Subgroup =
    is-prop-right-sim-Subgroup G (subgroup-Normal-Subgroup G N)

  prop-congruence-Normal-Subgroup : (x y : type-Group G) → UU-Prop (l1 ⊔ l2)
  prop-congruence-Normal-Subgroup =
    prop-right-eq-rel-Subgroup G (subgroup-Normal-Subgroup G N)

  refl-congruence-Normal-Subgroup :
    is-reflexive-Rel-Prop prop-congruence-Normal-Subgroup
  refl-congruence-Normal-Subgroup =
    refl-right-sim-Subgroup G (subgroup-Normal-Subgroup G N)

  symm-congruence-Normal-Subgroup :
    is-symmetric-Rel-Prop prop-congruence-Normal-Subgroup
  symm-congruence-Normal-Subgroup =
    symm-right-sim-Subgroup G (subgroup-Normal-Subgroup G N)

  trans-congruence-Normal-Subgroup :
    is-transitive-Rel-Prop prop-congruence-Normal-Subgroup
  trans-congruence-Normal-Subgroup =
    trans-right-sim-Subgroup G (subgroup-Normal-Subgroup G N)

  eq-rel-congruence-Normal-Subgroup : Eq-Rel (l1 ⊔ l2) (type-Group G)
  eq-rel-congruence-Normal-Subgroup =
    right-eq-rel-Subgroup G (subgroup-Normal-Subgroup G N)

  is-congruence-eq-rel-congruence-Normal-Subgroup :
    is-congruence-Eq-Rel-Group G eq-rel-congruence-Normal-Subgroup
  pr1
    ( is-congruence-eq-rel-congruence-Normal-Subgroup
      {x} {x'} {y} {y'} (u , p) (v , q)) =
    mul-Normal-Subgroup G N (conjugation-Normal-Subgroup' G N y u) v
  pr2
    ( is-congruence-eq-rel-congruence-Normal-Subgroup
      {x1 = x} {y1 = y} (u , p) (v , q)) =
    ( ( associative-mul-Group G x y
        ( inclusion-Normal-Subgroup G N
          ( mul-Normal-Subgroup G N
            ( conjugation-Normal-Subgroup' G N y u)
            ( v)))) ∙
      ( ( ap
          ( mul-Group G x)
          ( inv
            ( associative-mul-Group G
              ( y)
              ( inclusion-Normal-Subgroup G N
                ( conjugation-Normal-Subgroup' G N y u))
              ( inclusion-Normal-Subgroup G N v)) ∙
            ( ( ap
                ( mul-Group' G (inclusion-Normal-Subgroup G N v))
                ( right-conjugation-law-mul-Group' G y
                  ( inclusion-Normal-Subgroup G N u))) ∙
              ( associative-mul-Group G
                ( inclusion-Normal-Subgroup G N u)
                ( y)
                ( inclusion-Normal-Subgroup G N v))))) ∙
        ( inv
          ( associative-mul-Group G x
            ( inclusion-Normal-Subgroup G N u)
            ( mul-Group G y (inclusion-Normal-Subgroup G N v)))))) ∙
    ( ap-mul-Group G p q)

  congruence-Normal-Subgroup : congruence-Group (l1 ⊔ l2) G
  pr1 congruence-Normal-Subgroup = eq-rel-congruence-Normal-Subgroup
  pr2 congruence-Normal-Subgroup =
    is-congruence-eq-rel-congruence-Normal-Subgroup
```
