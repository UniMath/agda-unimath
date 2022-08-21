---
title: Congruence relations on groups
---

```agda
module group-theory.congruence-relations-groups where

open import foundation.binary-relations
open import foundation.dependent-pair-types
open import foundation.equivalence-relations
open import foundation.equivalences
open import foundation.identity-types
open import foundation.propositions
open import foundation.universe-levels

open import group-theory.congruence-relations-semigroups
open import group-theory.conjugation
open import group-theory.groups
```

## Idea

A congruence relation on a group `G` is an equivalence relation `≡` on `G` such that for every `x1 x2 y1 y2 : G` such that `x1 ≡ x2` and `y1 ≡ y2` we have `x1 · y1 ≡ x2 · y2`.

## Definition

```agda
is-congruence-Eq-Rel-Group :
  {l1 l2 : Level} (G : Group l1) → Eq-Rel l2 (type-Group G) → UU (l1 ⊔ l2)
is-congruence-Eq-Rel-Group G R =
  is-congruence-Eq-Rel-Semigroup (semigroup-Group G) R

congruence-Group : {l : Level} (l2 : Level) (G : Group l) → UU (l ⊔ lsuc l2)
congruence-Group l2 G =
  Σ (Eq-Rel l2 (type-Group G)) (is-congruence-Eq-Rel-Group G)

module _
  {l1 l2 : Level} (G : Group l1) (R : congruence-Group l2 G)
  where

  eq-rel-congruence-Group : Eq-Rel l2 (type-Group G)
  eq-rel-congruence-Group = pr1 R

  prop-congruence-Group : Rel-Prop l2 (type-Group G)
  prop-congruence-Group = prop-Eq-Rel eq-rel-congruence-Group

  sim-congruence-Group : (x y : type-Group G) → UU l2
  sim-congruence-Group = sim-Eq-Rel eq-rel-congruence-Group

  is-prop-sim-congruence-Group :
    (x y : type-Group G) → is-prop (sim-congruence-Group x y)
  is-prop-sim-congruence-Group = is-prop-sim-Eq-Rel eq-rel-congruence-Group

  concatenate-eq-sim-congruence-Group :
    {x1 x2 y : type-Group G} →
    x1 ＝ x2 → sim-congruence-Group x2 y → sim-congruence-Group x1 y
  concatenate-eq-sim-congruence-Group refl H = H

  concatenate-sim-eq-congruence-Group :
    {x y1 y2 : type-Group G} →
    sim-congruence-Group x y1 → y1 ＝ y2 → sim-congruence-Group x y2
  concatenate-sim-eq-congruence-Group H refl = H

  concatenate-eq-sim-eq-congruence-Group :
    {x1 x2 y1 y2 : type-Group G} →
    x1 ＝ x2 → sim-congruence-Group x2 y1 → y1 ＝ y2 → sim-congruence-Group x1 y2
  concatenate-eq-sim-eq-congruence-Group refl H refl = H
  
  refl-congruence-Group : is-reflexive-Rel-Prop prop-congruence-Group
  refl-congruence-Group = refl-Eq-Rel eq-rel-congruence-Group

  symm-congruence-Group : is-symmetric-Rel-Prop prop-congruence-Group
  symm-congruence-Group = symm-Eq-Rel eq-rel-congruence-Group

  equiv-symm-congruence-Group :
    (x y : type-Group G) → sim-congruence-Group x y ≃ sim-congruence-Group y x
  equiv-symm-congruence-Group = equiv-symm-Eq-Rel eq-rel-congruence-Group

  trans-congruence-Group : is-transitive-Rel-Prop prop-congruence-Group
  trans-congruence-Group = trans-Eq-Rel eq-rel-congruence-Group

  mul-congruence-Group : is-congruence-Eq-Rel-Group G eq-rel-congruence-Group
  mul-congruence-Group = pr2 R

  left-mul-congruence-Group :
    (x : type-Group G) {y z : type-Group G} → sim-congruence-Group y z →
    sim-congruence-Group (mul-Group G x y) (mul-Group G x z)
  left-mul-congruence-Group x H =
    mul-congruence-Group refl-congruence-Group H

  right-mul-congruence-Group :
    {x y : type-Group G} → sim-congruence-Group x y → (z : type-Group G) →
    sim-congruence-Group (mul-Group G x z) (mul-Group G y z)
  right-mul-congruence-Group H z =
    mul-congruence-Group H refl-congruence-Group

  conjugation-congruence-Group :
    (x : type-Group G) {y z : type-Group G} → sim-congruence-Group y z →
    sim-congruence-Group (conjugation-Group G x y) (conjugation-Group G x z)
  conjugation-congruence-Group x H =
    right-mul-congruence-Group (left-mul-congruence-Group x H) (inv-Group G x)

  conjugation-congruence-Group' :
    (x : type-Group G) {y z : type-Group G} → sim-congruence-Group y z →
    sim-congruence-Group (conjugation-Group' G x y) (conjugation-Group' G x z)
  conjugation-congruence-Group' x H =
    right-mul-congruence-Group (left-mul-congruence-Group (inv-Group G x) H) x

  sim-congruence-Group' : (x y : type-Group G) → UU l2
  sim-congruence-Group' x y =
    sim-congruence-Group (mul-Group G x (inv-Group G y)) (unit-Group G)

  map-sim-congruence-Group' :
    {x y : type-Group G} → sim-congruence-Group x y → sim-congruence-Group' x y
  map-sim-congruence-Group' {x} {y} H =
    concatenate-sim-eq-congruence-Group
      ( right-mul-congruence-Group H (inv-Group G y))
      ( right-inverse-law-Group G y)

  map-inv-sim-congruence-Group' :
    {x y : type-Group G} → sim-congruence-Group' x y → sim-congruence-Group x y
  map-inv-sim-congruence-Group' {x} {y} H =
    concatenate-eq-sim-eq-congruence-Group
      ( inv
        ( ( associative-mul-Group G x (inv-Group G y) y) ∙
          ( ( ap (mul-Group G x) (left-inverse-law-Group G y)) ∙
            ( right-unit-law-Group G x))))
      ( right-mul-congruence-Group H y)
      ( left-unit-law-Group G y)

  inv-congruence-Group :
    {x y : type-Group G} →
    sim-congruence-Group x y →
    sim-congruence-Group (inv-Group G x) (inv-Group G y)
  inv-congruence-Group {x} {y} H =
    concatenate-eq-sim-eq-congruence-Group
      ( inv
        ( ( associative-mul-Group G (inv-Group G x) y (inv-Group G y)) ∙
          ( ( ap (mul-Group G (inv-Group G x)) (right-inverse-law-Group G y)) ∙
            ( right-unit-law-Group G (inv-Group G x)))))
      ( symm-congruence-Group
        ( right-mul-congruence-Group
          ( left-mul-congruence-Group (inv-Group G x) H)
          ( inv-Group G y)))
      ( ( ap (mul-Group' G (inv-Group G y)) (left-inverse-law-Group G x)) ∙
        ( left-unit-law-Group G (inv-Group G y)))
```
