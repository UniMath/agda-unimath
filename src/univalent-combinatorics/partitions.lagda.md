---
title: Partitions of finite types
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module univalent-combinatorics.partitions where

open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.inhabited-types
open import foundation.propositional-truncations
open import foundation.universe-levels

open import univalent-combinatorics.dependent-sum-finite-types
open import univalent-combinatorics.finite-types
```

## Idea

A partition of a finite type `X` can be defined in several equivalent ways:

- A partition is a subset `P` of the powerset of `X` such that each `U ⊆ X` in `P` is inhabited and each element `x : X` is in exactly one subset `U ⊆ X` in `P`.
- A partition is an equivalence relation on `X`
- A partition is a decomposition of `X` into a type of the form `Σ A B` where `A` is finite and `B` is a family of inhabited finite types, i.e., it consists of such `A` and `B` and an equivalence `X ≃ Σ A B`.

Note that the last description is subtly different from the notion of unlabeled partition (i.e., Ferrers diagram), because it only uses mere equivalences.

### Definition

```agda
partition-𝔽 : 𝔽 → UU (lsuc lzero)
partition-𝔽 X =
  Σ 𝔽
    ( λ Y →
      Σ ( type-𝔽 Y → 𝔽)
        ( λ Z →
          ( (y : type-𝔽 Y) → type-trunc-Prop (type-𝔽 (Z y))) ×
          ( equiv-𝔽 X (Σ-𝔽 Y Z))))

module _
  (X : 𝔽) (P : partition-𝔽 X)
  where

  finite-indexing-type-partition-𝔽 : 𝔽
  finite-indexing-type-partition-𝔽 = pr1 P

  indexing-type-partition-𝔽 : UU lzero
  indexing-type-partition-𝔽 = type-𝔽 finite-indexing-type-partition-𝔽

  finite-block-partition-𝔽 : indexing-type-partition-𝔽 → 𝔽
  finite-block-partition-𝔽 = pr1 (pr2 P)

  block-partition-𝔽 : indexing-type-partition-𝔽 → UU lzero
  block-partition-𝔽 i = type-𝔽 (finite-block-partition-𝔽 i)

  is-inhabited-block-partition-𝔽 :
    (i : indexing-type-partition-𝔽) → type-trunc-Prop (block-partition-𝔽 i)
  is-inhabited-block-partition-𝔽 = pr1 (pr2 (pr2 P))

  equiv-partition-𝔽 :
    equiv-𝔽 X (Σ-𝔽 finite-indexing-type-partition-𝔽 finite-block-partition-𝔽)
  equiv-partition-𝔽 = pr2 (pr2 (pr2 P))
```
