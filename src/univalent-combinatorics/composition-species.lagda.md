---
title: Composition of species
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module univalent-combinatorics.composition-species where

open import foundation.cartesian-product-types
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.identity-types
open import foundation.propositional-truncations
open import foundation.universe-levels

open import univalent-combinatorics.dependent-sum-finite-types
open import univalent-combinatorics.equivalences-species
open import univalent-combinatorics.finite-types
open import univalent-combinatorics.species
```

## Idea

A species `S : 𝔽 → UU l` can be thought of as the analytic endofunctor

```md
  X ↦ Σ (A : 𝔽) (S A) × (A → X)
```

Using the formula for composition of analytic endofunctors, we obtain a way to compose species.

## Definition

### Analytic composition of species

```agda
analytic-comp-species :
  {l1 l2 : Level} → species l1 → species l2 → species (lsuc lzero ⊔ l1 ⊔ l2)
analytic-comp-species S T X =
  Σ ( 𝔽)
    ( λ Y →
      Σ ( Σ ( type-𝔽 Y → 𝔽)
            ( λ Z → (y : type-𝔽 Y) → type-trunc-Prop (type-𝔽 (Z y))))
        ( λ Z →
          ( (type-𝔽 (Σ-𝔽 Y (pr1 Z)) ≃ type-𝔽 X)) ×
          ( T Y × ((y : type-𝔽 Y) → S (pr1 Z y)))))
```

### The analytic unit for composition of species

```agda
analytic-unit-species : species lzero
analytic-unit-species X = is-contr (type-𝔽 X)
```

## Properties

### Unit laws for analytic composition of species

```agda
left-unit-law-comp-species :
  {l : Level} (F : species l) →
  equiv-species (analytic-comp-species analytic-unit-species F) F
left-unit-law-comp-species F X =
  {!!}
```
