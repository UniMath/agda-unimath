---
title: The Zarisky topology on a space
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module commutative-algebra.zarisky-topology where

open import foundation.dependent-pair-types
open import foundation.existential-quantification
open import foundation.identity-types
open import foundation.powersets
open import foundation.propositions
open import foundation.subtypes
open import foundation.universe-levels

open import commutative-algebra.commutative-rings
open import commutative-algebra.prime-ideals-commutative-rings
```

## Idea

The Zarisky topology on the set of prime ideals in a commutative ring is described by what the closed sets are: A subset `I` of prime ideals is closed if it is the intersection of all the prime ideals that

## Definitions

### Closed subsets in the Zarisky topology

```agda
standard-closed-subset-zarisky-topology-Commutative-Ring :
  {l1 l2 l3 : Level} (R : Commutative-Ring l1) →
  subtype l3 (type-Commutative-Ring R) →
  subtype (l1 ⊔ l2 ⊔ l3) (prime-ideal-Commutative-Ring l2 R)
standard-closed-subset-zarisky-topology-Commutative-Ring R U P =
  inclusion-rel-subtype-Prop U (subset-prime-ideal-Commutative-Ring R P)

is-closed-subset-zarisky-topology-Commutative-Ring :
  {l1 l2 l3 : Level} (R : Commutative-Ring l1)
  (U : subtype (l1 ⊔ l2 ⊔ l3) (prime-ideal-Commutative-Ring l2 R)) →
  UU-Prop (lsuc l1 ⊔ lsuc l2 ⊔ lsuc l3)
is-closed-subset-zarisky-topology-Commutative-Ring {l1} {l2} {l3} R U =
  ∃-Prop
    ( λ (V : subtype l3 (type-Commutative-Ring R)) →
      Id (standard-closed-subset-zarisky-topology-Commutative-Ring R V) U)

closed-subset-zarisky-topology-Commutative-Ring :
  {l1 l2 : Level} (l3 : Level) (R : Commutative-Ring l1) →
  UU (lsuc l1 ⊔ lsuc l2 ⊔ lsuc l3)
closed-subset-zarisky-topology-Commutative-Ring {l1} {l2} l3 R =
  type-subtype
    ( is-closed-subset-zarisky-topology-Commutative-Ring {l1} {l2} {l3} R)
```
