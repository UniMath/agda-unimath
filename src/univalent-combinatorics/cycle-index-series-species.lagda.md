---
title: Cycle index series of species
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module univalent-combinatorics.cycle-index-series-species where

open import elementary-number-theory.natural-numbers

open import foundation.automorphisms
open import foundation.dependent-pair-types
open import foundation.functions
open import foundation.universe-levels

open import synthetic-homotopy-theory.cyclic-types

open import univalent-combinatorics.finite-types
open import univalent-combinatorics.species
```

## Idea

The cycle index series of a species `F` is a type family indexed by finite families of cyclic types. Note that a finite family of cyclic types `Cᵢ` uniquely determines a permutation `e` on the disjoint union `C := Σᵢ Cᵢ` of the underlying types of the `Cᵢ`. This permutation determines an action `F e` on `F C`. The cycle index series of `F` at the family `Cᵢ` is the type `Fix (F e)` of fixed points of `F e`.

## Definition

```agda
total-type-family-of-cyclic-types :
  {l : Level} (X : 𝔽) (C : type-𝔽 X → Σ ℕ (Cyclic l)) → UU l
total-type-family-of-cyclic-types X C =
  Σ (type-𝔽 X) (λ x → type-Cyclic (pr1 (C x)) (pr2 (C x)))

permutation-family-of-cyclic-types :
  {l : Level} (X : 𝔽) (C : type-𝔽 X → Σ ℕ (Cyclic l)) →
  Aut (total-type-family-of-cyclic-types X C)
permutation-family-of-cyclic-types X C = {!!}

cycle-index-series-species :
  {l : Level} (F : species l) (X : 𝔽) →
  (type-𝔽 X → Σ ℕ (Cyclic lzero ∘ succ-ℕ)) →
  UU {!!}
cycle-index-series-species F X C = Σ {!F (total-type-family-of-cyclic-types X C)!} {!!}
```
