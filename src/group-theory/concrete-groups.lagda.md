---
title: Concrete groups
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module group-theory.concrete-groups where

open import foundation.0-connected-types using (is-0-connected)
open import foundation.1-types using (Id-Set)
open import foundation.dependent-pair-types using (Σ; pr1; pr2; pair)
open import foundation.equivalences using (_≃_; map-inv-equiv)
open import foundation.identity-types using (Id; refl)
open import foundation.mere-equality using (mere-eq)
open import foundation.propositional-truncations using
  ( apply-universal-property-trunc-Prop)
open import foundation.propositions using (Prop; type-Prop)
open import foundation.sets using (is-set; Set; is-set-Prop)
open import foundation.truncated-types using (is-trunc; Truncated-Type)
open import foundation.truncation-levels using (one-𝕋)
open import foundation.universe-levels using (UU; Level; _⊔_; lsuc)

open import group-theory.groups using (Group)
open import group-theory.higher-groups using
  ( ∞-Group; type-∞-Group; classifying-pointed-type-∞-Group;
    classifying-type-∞-Group; shape-∞-Group;
    is-0-connected-classifying-type-∞-Group;
    mere-eq-classifying-type-∞-Group;
    elim-prop-classifying-type-∞-Group;
    unit-∞-Group; mul-∞-Group; assoc-mul-∞-Group;
    left-unit-law-mul-∞-Group; right-unit-law-mul-∞-Group;
    coherence-unit-laws-mul-∞-Group; inv-∞-Group;
    left-inverse-law-mul-∞-Group; right-inverse-law-mul-∞-Group)
open import group-theory.homomorphisms-groups using (type-hom-Group)
open import group-theory.homomorphisms-higher-groups using
  ( hom-∞-Group; classifying-map-hom-∞-Group;
    preserves-point-classifying-map-hom-∞-Group;
    map-hom-∞-Group; preserves-unit-map-hom-∞-Group;
    preserves-mul-map-hom-∞-Group; preserves-inv-map-hom-∞-Group;
    htpy-hom-∞-Group; extensionality-hom-∞-Group;
    id-hom-∞-Group; comp-hom-∞-Group; assoc-comp-hom-∞-Group;
    left-unit-law-comp-hom-∞-Group; right-unit-law-comp-hom-∞-Group)

open import structured-types.pointed-types using (Pointed-Type)

Concrete-Group : (l : Level) → UU (lsuc l)
Concrete-Group l = Σ (∞-Group l) (λ G → is-set (type-∞-Group G))

module _
  {l : Level} (G : Concrete-Group l)
  where

  ∞-group-Concrete-Group : ∞-Group l
  ∞-group-Concrete-Group = pr1 G

  classifying-pointed-type-Concrete-Group : Pointed-Type l
  classifying-pointed-type-Concrete-Group =
    classifying-pointed-type-∞-Group ∞-group-Concrete-Group

  classifying-type-Concrete-Group : UU l
  classifying-type-Concrete-Group =
    classifying-type-∞-Group ∞-group-Concrete-Group

  shape-Concrete-Group : classifying-type-Concrete-Group
  shape-Concrete-Group =
    shape-∞-Group ∞-group-Concrete-Group

  is-0-connected-classifying-type-Concrete-Group :
    is-0-connected classifying-type-Concrete-Group
  is-0-connected-classifying-type-Concrete-Group =
    is-0-connected-classifying-type-∞-Group ∞-group-Concrete-Group

  mere-eq-classifying-type-Concrete-Group :
    (X Y : classifying-type-Concrete-Group) → mere-eq X Y
  mere-eq-classifying-type-Concrete-Group =
    mere-eq-classifying-type-∞-Group ∞-group-Concrete-Group

  elim-prop-classifying-type-Concrete-Group :
    {l2 : Level} (P : classifying-type-Concrete-Group → Prop l2) →
    type-Prop (P shape-Concrete-Group) →
    ((X : classifying-type-Concrete-Group) → type-Prop (P X))
  elim-prop-classifying-type-Concrete-Group =
    elim-prop-classifying-type-∞-Group ∞-group-Concrete-Group

  type-Concrete-Group : UU l
  type-Concrete-Group = type-∞-Group ∞-group-Concrete-Group

  is-set-type-Concrete-Group : is-set type-Concrete-Group
  is-set-type-Concrete-Group = pr2 G

  set-Concrete-Group : Set l
  set-Concrete-Group = pair type-Concrete-Group is-set-type-Concrete-Group

  is-1-type-classifying-type-Concrete-Group :
    is-trunc one-𝕋 classifying-type-Concrete-Group
  is-1-type-classifying-type-Concrete-Group X Y =
    apply-universal-property-trunc-Prop
      ( mere-eq-classifying-type-Concrete-Group shape-Concrete-Group X)
      ( is-set-Prop (Id X Y))
      ( λ { refl →
            apply-universal-property-trunc-Prop
              ( mere-eq-classifying-type-Concrete-Group shape-Concrete-Group Y)
              ( is-set-Prop (Id shape-Concrete-Group Y))
              ( λ { refl → is-set-type-Concrete-Group})})

  classifying-1-type-Concrete-Group : Truncated-Type l one-𝕋
  classifying-1-type-Concrete-Group =
    pair
      classifying-type-Concrete-Group
      is-1-type-classifying-type-Concrete-Group

  Id-BG-Set :
    (X Y : classifying-type-Concrete-Group) → Set l
  Id-BG-Set X Y = Id-Set classifying-1-type-Concrete-Group X Y

  unit-Concrete-Group : type-Concrete-Group
  unit-Concrete-Group = unit-∞-Group ∞-group-Concrete-Group

  mul-Concrete-Group : (x y : type-Concrete-Group) → type-Concrete-Group
  mul-Concrete-Group = mul-∞-Group ∞-group-Concrete-Group

  assoc-mul-Concrete-Group :
    (x y z : type-Concrete-Group) →
    Id (mul-Concrete-Group (mul-Concrete-Group x y) z)
       (mul-Concrete-Group x (mul-Concrete-Group y z))
  assoc-mul-Concrete-Group = assoc-mul-∞-Group ∞-group-Concrete-Group

  left-unit-law-mul-Concrete-Group :
    (x : type-Concrete-Group) → Id (mul-Concrete-Group unit-Concrete-Group x) x
  left-unit-law-mul-Concrete-Group =
    left-unit-law-mul-∞-Group ∞-group-Concrete-Group

  right-unit-law-mul-Concrete-Group :
    (y : type-Concrete-Group) → Id (mul-Concrete-Group y unit-Concrete-Group) y
  right-unit-law-mul-Concrete-Group =
    right-unit-law-mul-∞-Group ∞-group-Concrete-Group

  coherence-unit-laws-mul-Concrete-Group :
    Id ( left-unit-law-mul-Concrete-Group unit-Concrete-Group)
       ( right-unit-law-mul-Concrete-Group unit-Concrete-Group)
  coherence-unit-laws-mul-Concrete-Group =
    coherence-unit-laws-mul-∞-Group ∞-group-Concrete-Group

  inv-Concrete-Group : type-Concrete-Group → type-Concrete-Group
  inv-Concrete-Group = inv-∞-Group ∞-group-Concrete-Group

  left-inverse-law-mul-Concrete-Group :
    (x : type-Concrete-Group) →
    Id (mul-Concrete-Group (inv-Concrete-Group x) x) unit-Concrete-Group
  left-inverse-law-mul-Concrete-Group =
    left-inverse-law-mul-∞-Group ∞-group-Concrete-Group

  right-inverse-law-mul-Concrete-Group :
    (x : type-Concrete-Group) →
    Id (mul-Concrete-Group x (inv-Concrete-Group x)) unit-Concrete-Group
  right-inverse-law-mul-Concrete-Group =
    right-inverse-law-mul-∞-Group ∞-group-Concrete-Group

  abstract-group-Concrete-Group : Group l
  abstract-group-Concrete-Group =
    pair
      ( pair
        ( set-Concrete-Group)
        ( pair
          mul-Concrete-Group
          assoc-mul-Concrete-Group))
      ( pair
        ( pair
          ( unit-Concrete-Group)
          ( pair
            left-unit-law-mul-Concrete-Group
            right-unit-law-mul-Concrete-Group))
        ( pair
          ( inv-Concrete-Group)
          ( pair
            left-inverse-law-mul-Concrete-Group
            right-inverse-law-mul-Concrete-Group)))

```
