# Joins of finite families of elements in join-semilattices

```agda
module order-theory.join-semilattices where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.binary-relations
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.propositions
open import foundation.sets
open import foundation.subtypes
open import foundation.universe-levels

open import group-theory.semigroups
open import group-theory.commutative-semigroups

open import order-theory.least-upper-bounds-posets
open import order-theory.posets
open import order-theory.preorders
open import order-theory.upper-bounds-posets
open import univalent-combinatorics.finite-types
open import univalent-combinatorics.inhabited-finite-types
```

</details>

## Idea

In a [join semilattice](order-theory.join-semilattices.md), we can define the
join of any family of elements indexed by an
[inhabited finite type](univalent-combinatorics.inhabited-finite-types.md).

## Definition

```agda
module _
  {l : Level} (X : Join-Semilattice l)
  where

  join-inhabited-finite-family-Join-Semilattice :
    {l2 : Level} (X : Inhabited-Finite-Type l2)
```
