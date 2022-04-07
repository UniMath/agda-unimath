---
title: Wild inverse semigroups
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module wild-algebra.wild-inverse-semigroups where

open import foundation.automorphisms
open import foundation.binary-equivalences
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.identity-types
open import foundation.universe-levels

open import wild-algebra.magmas
open import wild-algebra.wild-quasigroups
open import wild-algebra.wild-semigroups
```

## Idea

A wild inverse semigroup is a wild semigroup of which the binary operation is a binary equivalence

## Definition

```agda
Wild-Inverse-Semigroup : (l : Level) → UU (lsuc l)
Wild-Inverse-Semigroup l =
  Σ (Wild-Semigroup l) (λ G → is-binary-equiv (mul-Wild-Semigroup G))

module _
  {l : Level} (G : Wild-Inverse-Semigroup l)
  where

  wild-semigroup-Wild-Inverse-Semigroup : Wild-Semigroup l
  wild-semigroup-Wild-Inverse-Semigroup = pr1 G

  magma-Wild-Inverse-Semigroup : Magma l
  magma-Wild-Inverse-Semigroup =
    magma-Wild-Semigroup wild-semigroup-Wild-Inverse-Semigroup

  type-Wild-Inverse-Semigroup : UU l
  type-Wild-Inverse-Semigroup =
    type-Wild-Semigroup wild-semigroup-Wild-Inverse-Semigroup

  mul-Wild-Inverse-Semigroup :
    (x y : type-Wild-Inverse-Semigroup) → type-Wild-Inverse-Semigroup
  mul-Wild-Inverse-Semigroup =
    mul-Wild-Semigroup wild-semigroup-Wild-Inverse-Semigroup

  mul-Wild-Inverse-Semigroup' :
    (x y : type-Wild-Inverse-Semigroup) → type-Wild-Inverse-Semigroup
  mul-Wild-Inverse-Semigroup' =
    mul-Wild-Semigroup' wild-semigroup-Wild-Inverse-Semigroup

  associative-mul-Wild-Inverse-Semigroup :
    (x y z : type-Wild-Inverse-Semigroup) →
    Id ( mul-Wild-Inverse-Semigroup (mul-Wild-Inverse-Semigroup x y) z)
       ( mul-Wild-Inverse-Semigroup x (mul-Wild-Inverse-Semigroup y z))
  associative-mul-Wild-Inverse-Semigroup =
    associative-mul-Wild-Semigroup wild-semigroup-Wild-Inverse-Semigroup

  is-binary-equiv-mul-Wild-Inverse-Semigroup :
    is-binary-equiv mul-Wild-Inverse-Semigroup
  is-binary-equiv-mul-Wild-Inverse-Semigroup = pr2 G

  wild-quasigroup-Wild-Inverse-Semigroup : Wild-Quasigroup l
  pr1 wild-quasigroup-Wild-Inverse-Semigroup = magma-Wild-Inverse-Semigroup
  pr2 wild-quasigroup-Wild-Inverse-Semigroup =
    is-binary-equiv-mul-Wild-Inverse-Semigroup

  is-equiv-mul-Wild-Inverse-Semigroup :
    (x : type-Wild-Inverse-Semigroup) → is-equiv (mul-Wild-Inverse-Semigroup x)
  is-equiv-mul-Wild-Inverse-Semigroup =
    is-equiv-mul-Wild-Quasigroup wild-quasigroup-Wild-Inverse-Semigroup

  equiv-mul-Wild-Inverse-Semigroup :
    type-Wild-Inverse-Semigroup → Aut type-Wild-Inverse-Semigroup
  equiv-mul-Wild-Inverse-Semigroup =
    equiv-mul-Wild-Quasigroup wild-quasigroup-Wild-Inverse-Semigroup

  is-equiv-mul-Wild-Inverse-Semigroup' :
    (x : type-Wild-Inverse-Semigroup) → is-equiv (mul-Wild-Inverse-Semigroup' x)
  is-equiv-mul-Wild-Inverse-Semigroup' =
    is-equiv-mul-Wild-Quasigroup' wild-quasigroup-Wild-Inverse-Semigroup

  equiv-mul-Wild-Inverse-Semigroup' :
    type-Wild-Inverse-Semigroup → Aut type-Wild-Inverse-Semigroup
  equiv-mul-Wild-Inverse-Semigroup' =
    equiv-mul-Wild-Quasigroup' wild-quasigroup-Wild-Inverse-Semigroup
```
