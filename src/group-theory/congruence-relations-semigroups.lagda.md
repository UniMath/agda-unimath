---
title: Congruence relations on semigroups
---

```agda
module group-theory.congruence-relations-semigroups where

open import foundation.binary-relations
open import foundation.dependent-pair-types
open import foundation.equivalence-relations
open import foundation.equivalences
open import foundation.propositions
open import foundation.universe-levels

open import group-theory.semigroups
```

## Idea

A congruence relation on a semigroup `G` is an equivalence relation `≡` on `G` such that for every `x1 x2 y1 y2 : G` such that `x1 ≡ x2` and `y1 ≡ y2` we have `x1 · y1 ≡ x2 · y2`.

## Definition

```agda
is-congruence-Eq-Rel-Semigroup :
  {l1 l2 : Level} (G : Semigroup l1) → Eq-Rel l2 (type-Semigroup G) → UU (l1 ⊔ l2)
is-congruence-Eq-Rel-Semigroup G R =
  {x1 x2 y1 y2 : type-Semigroup G} → sim-Eq-Rel R x1 x2 → sim-Eq-Rel R y1 y2 →
  sim-Eq-Rel R (mul-Semigroup G x1 y1) (mul-Semigroup G x2 y2)

congruence-Semigroup : {l : Level} (l2 : Level) (G : Semigroup l) → UU (l ⊔ lsuc l2)
congruence-Semigroup l2 G =
  Σ (Eq-Rel l2 (type-Semigroup G)) (is-congruence-Eq-Rel-Semigroup G)

module _
  {l1 l2 : Level} (G : Semigroup l1) (R : congruence-Semigroup l2 G)
  where

  eq-rel-congruence-Semigroup : Eq-Rel l2 (type-Semigroup G)
  eq-rel-congruence-Semigroup = pr1 R

  prop-congruence-Semigroup : Rel-Prop l2 (type-Semigroup G)
  prop-congruence-Semigroup = prop-Eq-Rel eq-rel-congruence-Semigroup

  sim-congruence-Semigroup : (x y : type-Semigroup G) → UU l2
  sim-congruence-Semigroup = sim-Eq-Rel eq-rel-congruence-Semigroup

  is-prop-sim-congruence-Semigroup :
    (x y : type-Semigroup G) → is-prop (sim-congruence-Semigroup x y)
  is-prop-sim-congruence-Semigroup = is-prop-sim-Eq-Rel eq-rel-congruence-Semigroup

  refl-congruence-Semigroup : is-reflexive-Rel-Prop prop-congruence-Semigroup
  refl-congruence-Semigroup = refl-Eq-Rel eq-rel-congruence-Semigroup

  symm-congruence-Semigroup : is-symmetric-Rel-Prop prop-congruence-Semigroup
  symm-congruence-Semigroup = symm-Eq-Rel eq-rel-congruence-Semigroup

  equiv-symm-congruence-Semigroup :
    (x y : type-Semigroup G) → sim-congruence-Semigroup x y ≃ sim-congruence-Semigroup y x
  equiv-symm-congruence-Semigroup x y = equiv-symm-Eq-Rel eq-rel-congruence-Semigroup

  trans-congruence-Semigroup : is-transitive-Rel-Prop prop-congruence-Semigroup
  trans-congruence-Semigroup = trans-Eq-Rel eq-rel-congruence-Semigroup

  mul-congruence-Semigroup : is-congruence-Eq-Rel-Semigroup G eq-rel-congruence-Semigroup
  mul-congruence-Semigroup = pr2 R
```
