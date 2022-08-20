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

  is-emb-inclusion-Normal-Subgroup : is-emb inclusion-Normal-Subgroup
  is-emb-inclusion-Normal-Subgroup = is-emb-inclusion-Subgroup G subgroup-Normal-Subgroup

  emb-inclusion-Normal-Subgroup : type-Normal-Subgroup ↪ type-Group G
  emb-inclusion-Normal-Subgroup = emb-inclusion-Subgroup G subgroup-Normal-Subgroup

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
  unit-Normal-Subgroup = unit-group-Subgroup G subgroup-Normal-Subgroup

  is-closed-under-mul-Normal-Subgroup :
    is-closed-under-mul-subset-Group G subset-Normal-Subgroup
  is-closed-under-mul-Normal-Subgroup =
    is-closed-under-mul-Subgroup G subgroup-Normal-Subgroup

  mul-Normal-Subgroup : type-Normal-Subgroup → type-Normal-Subgroup → type-Normal-Subgroup
  mul-Normal-Subgroup = mul-group-Subgroup G subgroup-Normal-Subgroup

  is-closed-under-inv-Normal-Subgroup :
    is-closed-under-inv-subset-Group G subset-Normal-Subgroup
  is-closed-under-inv-Normal-Subgroup =
    is-closed-under-inv-Subgroup G subgroup-Normal-Subgroup

  inv-Normal-Subgroup : type-Normal-Subgroup → type-Normal-Subgroup
  inv-Normal-Subgroup = inv-group-Subgroup G subgroup-Normal-Subgroup

  group-Normal-Subgroup : Group (l1 ⊔ l2)
  group-Normal-Subgroup = group-Subgroup G subgroup-Normal-Subgroup
```

## Properties

### Normal subgroups are in 1-1 correspondence with congruence relations on groups

```agda
module _
  {l1 l2 : Level} (G : Group l1) (N : Normal-Subgroup l2 G)
  where
  
  sim-congruence-Normal-Subgroup : (x y : type-Group G) → UU (l1 ⊔ l2)
  sim-congruence-Normal-Subgroup x y =
    fib (mul-Group G x ∘ inclusion-Normal-Subgroup G N) y

  is-prop-sim-congruence-Normal-Subgroup :
    (x y : type-Group G) → is-prop (sim-congruence-Normal-Subgroup x y)
  is-prop-sim-congruence-Normal-Subgroup x =
    is-prop-map-is-emb
      ( is-emb-comp'
        ( mul-Group G x)
        ( inclusion-Normal-Subgroup G N)
        ( is-emb-mul-Group G x)
        ( is-emb-inclusion-Normal-Subgroup G N))

  prop-congruence-Normal-Subgroup : (x y : type-Group G) → UU-Prop (l1 ⊔ l2)
  pr1 (prop-congruence-Normal-Subgroup x y) = sim-congruence-Normal-Subgroup x y
  pr2 (prop-congruence-Normal-Subgroup x y) = is-prop-sim-congruence-Normal-Subgroup x y

  refl-congruence-Normal-Subgroup :
    is-reflexive-Rel-Prop prop-congruence-Normal-Subgroup
  pr1 (refl-congruence-Normal-Subgroup {x}) = unit-Normal-Subgroup G N
  pr2 (refl-congruence-Normal-Subgroup {x}) = right-unit-law-Group G x

  symm-congruence-Normal-Subgroup :
    is-symmetric-Rel-Prop prop-congruence-Normal-Subgroup
  pr1 (symm-congruence-Normal-Subgroup {x} {y} (u , p)) = inv-Normal-Subgroup G N u
  pr2 (symm-congruence-Normal-Subgroup {x} {y} (u , p)) = inv (transpose-eq-mul-Group G p)

  trans-congruence-Normal-Subgroup :
    is-transitive-Rel-Prop prop-congruence-Normal-Subgroup
  pr1 (trans-congruence-Normal-Subgroup {x} {y} {z} (u , p) (v , q)) =
    mul-Normal-Subgroup G N u v
  pr2 (trans-congruence-Normal-Subgroup {x} {y} {z} (u , p) (v , q)) =
    ( inv
      ( associative-mul-Group G x
        ( inclusion-Normal-Subgroup G N u)
        ( inclusion-Normal-Subgroup G N v))) ∙
    ( ( ap (mul-Group' G (inclusion-Normal-Subgroup G N v)) p) ∙
      ( q))

  eq-rel-congruence-Normal-Subgroup : Eq-Rel (l1 ⊔ l2) (type-Group G)
  pr1 eq-rel-congruence-Normal-Subgroup = prop-congruence-Normal-Subgroup
  pr1 (pr2 eq-rel-congruence-Normal-Subgroup) = refl-congruence-Normal-Subgroup
  pr1 (pr2 (pr2 eq-rel-congruence-Normal-Subgroup)) =
    symm-congruence-Normal-Subgroup
  pr2 (pr2 (pr2 eq-rel-congruence-Normal-Subgroup)) =
    trans-congruence-Normal-Subgroup
```
