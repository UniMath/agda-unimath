---
title: Cycle partitions of finite types
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module univalent-combinatorics.cycle-partitions where

open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.universe-levels

open import univalent-combinatorics.cyclic-types
open import univalent-combinatorics.dependent-sum-finite-types
open import univalent-combinatorics.finite-types
```

## Idea

A cycle partition of a finite type `A` is a finite family of cyclic finite types equipped with an equivalence from `A` to the total space of the underlying types of the family. The type of cyclic partitions of `A` is equivalent to the type of permutations of `A`.

## Definition

```agda
cyclic-partition-𝔽 : 𝔽 → UU (lsuc lzero)
cyclic-partition-𝔽 X =
  Σ 𝔽
    ( λ Y →
      Σ ( type-𝔽 Y → Σ ℕ (λ n → Cyclic-Type lzero (succ-ℕ n)))
        ( λ C →
          type-𝔽 X ≃
          Σ ( type-𝔽 Y)
            ( λ y → type-Cyclic-Type (succ-ℕ (pr1 (C y))) (pr2 (C y)))))

module _
  (X : 𝔽) (C : cyclic-partition-𝔽 X)
  where

  finite-indexing-type-cyclic-partition-𝔽 : 𝔽
  finite-indexing-type-cyclic-partition-𝔽 = pr1 C

  indexing-type-cyclic-partition-𝔽 : UU lzero
  indexing-type-cyclic-partition-𝔽 =
    type-𝔽 finite-indexing-type-cyclic-partition-𝔽

  order-cycle-cyclic-partition-𝔽 :
    indexing-type-cyclic-partition-𝔽 → ℕ
  order-cycle-cyclic-partition-𝔽 y = succ-ℕ (pr1 (pr1 (pr2 C) y))

  cycle-cyclic-partition-𝔽 :
    (y : indexing-type-cyclic-partition-𝔽) →
    Cyclic-Type lzero (order-cycle-cyclic-partition-𝔽 y)
  cycle-cyclic-partition-𝔽 y =
    pr2 (pr1 (pr2 C) y)

  type-cycle-cyclic-partition-𝔽 :
    indexing-type-cyclic-partition-𝔽 → UU lzero
  type-cycle-cyclic-partition-𝔽 y =
    type-Cyclic-Type
      ( order-cycle-cyclic-partition-𝔽 y)
      ( cycle-cyclic-partition-𝔽 y)

  equiv-cyclic-partition-𝔽 :
    type-𝔽 X ≃ Σ indexing-type-cyclic-partition-𝔽 type-cycle-cyclic-partition-𝔽
  equiv-cyclic-partition-𝔽 = pr2 (pr2 C)
```
