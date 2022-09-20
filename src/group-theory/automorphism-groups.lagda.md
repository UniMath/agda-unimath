---
title: Automorphism groups
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module group-theory.automorphism-groups where

open import foundation.0-connected-types
open import foundation.1-types
open import foundation.connected-components
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.propositional-truncations
open import foundation.truncated-types
open import foundation.truncation-levels
open import foundation.universe-levels

open import group-theory.concrete-groups
open import group-theory.higher-groups

open import structured-types.pointed-types
```

## Idea

The automorphim group of `a : A` is the group of symmetries of `a` in `A`.

## Definitions

### Automorphism ∞-groups of a type

```agda
module _
  {l : Level} (A : UU l) (a : A)
  where

  classifying-type-Automorphism-∞-Group : UU l
  classifying-type-Automorphism-∞-Group = connected-component A a

  shape-Automorphism-∞-Group : classifying-type-Automorphism-∞-Group
  pr1 shape-Automorphism-∞-Group = a
  pr2 shape-Automorphism-∞-Group = unit-trunc-Prop refl

  classifying-pointed-type-Automorphism-∞-Group : Pointed-Type l
  pr1 classifying-pointed-type-Automorphism-∞-Group =
    classifying-type-Automorphism-∞-Group
  pr2 classifying-pointed-type-Automorphism-∞-Group =
    shape-Automorphism-∞-Group

  is-0-connected-classifying-type-Automorphism-∞-Group :
    is-0-connected classifying-type-Automorphism-∞-Group
  is-0-connected-classifying-type-Automorphism-∞-Group =
    is-0-connected-connected-component A a
  
  Automorphism-∞-Group : ∞-Group l
  pr1 Automorphism-∞-Group = classifying-pointed-type-Automorphism-∞-Group
  pr2 Automorphism-∞-Group =
    is-0-connected-classifying-type-Automorphism-∞-Group
```

### Automorphism groups of a set

```agda
module _
  {l : Level} (A : 1-Type l) (a : type-1-Type A)
  where

  classifying-type-Automorphism-Group : UU l
  classifying-type-Automorphism-Group =
    classifying-type-Automorphism-∞-Group (type-1-Type A) a

  Automorphism-Group : Concrete-Group l
  pr1 Automorphism-Group = Automorphism-∞-Group (type-1-Type A) a
  pr2 Automorphism-Group = 
    is-trunc-connected-component
      ( type-1-Type A)
      ( a)
      ( is-1-type-type-1-Type A)
      ( pair a (unit-trunc-Prop refl))
      ( pair a (unit-trunc-Prop refl))
```

## Properties

### Characerizing the identity type of `Automorphism-∞-Group`

```agda
```
