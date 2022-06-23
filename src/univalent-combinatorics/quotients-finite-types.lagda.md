---
title: Quotients of finite types
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module univalent-combinatorics.quotients-finite-types where

open import foundation.equivalence-classes
open import foundation.universe-levels

open import univalent-combinatorics.decidable-equivalence-relations
open import univalent-combinatorics.image-of-maps
open import univalent-combinatorics.finite-types
```

## Idea

The quotient of a finite type by a decidable equivalence relation is again a finite type. In this file we set up some infrastructure for such quotients.

## Definition

```agda
module _
  (X : 𝔽) (R : Decidable-Equivalence-Relation-𝔽 X)
  where

  equivalence-class-Decidable-Equivalence-Relation-𝔽 : UU (lsuc lzero)
  equivalence-class-Decidable-Equivalence-Relation-𝔽 =
    equivalence-class
      ( equivalence-relation-Decidable-Equivalence-Relation-𝔽 X R)

  is-finite-equivalence-class-Decidable-Equivalence-Relation-𝔽' :
    is-finite equivalence-class-Decidable-Equivalence-Relation-𝔽
  is-finite-equivalence-class-Decidable-Equivalence-Relation-𝔽' =
    is-finite-im
      ( is-finite-type-𝔽 X)
      {!!}

  quotient-𝔽 : 𝔽
  quotient-𝔽 = {!!}
```
