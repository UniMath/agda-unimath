---
title: Higher groups
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module group-theory.higher-groups where

open import foundation.0-connected-types using
  ( is-0-connected; mere-eq-is-0-connected;
    apply-dependent-universal-property-is-0-connected)
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.identity-types
open import foundation.mere-equality
open import foundation.propositions
open import foundation.universe-levels

open import structured-types.pointed-homotopies using
  ( htpy-pointed-map; extensionality-pointed-map;
    assoc-comp-pointed-map; left-unit-law-comp-pointed-map;
    right-unit-law-comp-pointed-map)
open import structured-types.pointed-maps using
  ( _→*_; map-pointed-map; preserves-point-pointed-map;
    id-pointed-map; comp-pointed-map)
open import structured-types.pointed-types

open import synthetic-homotopy-theory.functoriality-loop-spaces using
  ( map-Ω; preserves-refl-map-Ω; preserves-mul-map-Ω;
    preserves-inv-map-Ω)
open import synthetic-homotopy-theory.loop-spaces using
  ( type-Ω; refl-Ω; mul-Ω; associative-mul-Ω; left-unit-law-mul-Ω;
    right-unit-law-mul-Ω; inv-Ω; left-inverse-law-mul-Ω;
    right-inverse-law-mul-Ω)
```

## Idea

An ∞-group is just a pointed connected type. Its underlying type is its loop space, and the classifying type is the pointed connected type itself.

## Definition

```agda
∞-Group : (l : Level) → UU (lsuc l)
∞-Group l = Σ (Pointed-Type l) (λ X → is-0-connected (type-Pointed-Type X))

module _
  {l : Level} (G : ∞-Group l)
  where

  classifying-pointed-type-∞-Group : Pointed-Type l
  classifying-pointed-type-∞-Group = pr1 G

  classifying-type-∞-Group : UU l
  classifying-type-∞-Group =
    type-Pointed-Type classifying-pointed-type-∞-Group

  shape-∞-Group : classifying-type-∞-Group
  shape-∞-Group =
    pt-Pointed-Type classifying-pointed-type-∞-Group

  is-0-connected-classifying-type-∞-Group :
    is-0-connected classifying-type-∞-Group
  is-0-connected-classifying-type-∞-Group = pr2 G

  mere-eq-classifying-type-∞-Group :
    (X Y : classifying-type-∞-Group) → mere-eq X Y
  mere-eq-classifying-type-∞-Group =
    mere-eq-is-0-connected
      is-0-connected-classifying-type-∞-Group

  elim-prop-classifying-type-∞-Group :
    {l2 : Level} (P : classifying-type-∞-Group → Prop l2) →
    type-Prop (P shape-∞-Group) →
    ((X : classifying-type-∞-Group) → type-Prop (P X))
  elim-prop-classifying-type-∞-Group =
    apply-dependent-universal-property-is-0-connected
      shape-∞-Group
      is-0-connected-classifying-type-∞-Group

  type-∞-Group : UU l
  type-∞-Group = type-Ω classifying-pointed-type-∞-Group

  unit-∞-Group : type-∞-Group
  unit-∞-Group = refl-Ω classifying-pointed-type-∞-Group

  mul-∞-Group : (x y : type-∞-Group) → type-∞-Group
  mul-∞-Group = mul-Ω classifying-pointed-type-∞-Group

  assoc-mul-∞-Group :
    (x y z : type-∞-Group) →
    Id (mul-∞-Group (mul-∞-Group x y) z)
       (mul-∞-Group x (mul-∞-Group y z))
  assoc-mul-∞-Group = associative-mul-Ω classifying-pointed-type-∞-Group

  left-unit-law-mul-∞-Group :
    (x : type-∞-Group) → Id (mul-∞-Group unit-∞-Group x) x
  left-unit-law-mul-∞-Group =
    left-unit-law-mul-Ω classifying-pointed-type-∞-Group

  right-unit-law-mul-∞-Group :
    (y : type-∞-Group) → Id (mul-∞-Group y unit-∞-Group) y
  right-unit-law-mul-∞-Group =
    right-unit-law-mul-Ω classifying-pointed-type-∞-Group

  coherence-unit-laws-mul-∞-Group :
    Id ( left-unit-law-mul-∞-Group unit-∞-Group)
       ( right-unit-law-mul-∞-Group unit-∞-Group)
  coherence-unit-laws-mul-∞-Group = refl

  inv-∞-Group : type-∞-Group → type-∞-Group
  inv-∞-Group = inv-Ω classifying-pointed-type-∞-Group

  left-inverse-law-mul-∞-Group :
    (x : type-∞-Group) → Id (mul-∞-Group (inv-∞-Group x) x) unit-∞-Group
  left-inverse-law-mul-∞-Group =
    left-inverse-law-mul-Ω classifying-pointed-type-∞-Group

  right-inverse-law-mul-∞-Group :
    (x : type-∞-Group) → Id (mul-∞-Group x (inv-∞-Group x)) unit-∞-Group
  right-inverse-law-mul-∞-Group =
    right-inverse-law-mul-Ω classifying-pointed-type-∞-Group
```
