# The weak limited principle of omniscience and increasing binary sequences

```agda
{-# OPTIONS --guardedness #-}

module set-theory.weak-limited-principle-of-omniscience-increasing-binary-sequences where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.equality-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.booleans
open import foundation.coproduct-types
open import foundation.decidable-equality
open import foundation.decidable-subtypes
open import foundation.dependent-pair-types
open import foundation.discrete-types
open import foundation.embeddings
open import foundation.equivalences
open import foundation.function-types
open import foundation.functoriality-coproduct-types
open import foundation.inequality-booleans
open import foundation.logical-equivalences
open import foundation.logical-operations-booleans
open import foundation.negated-equality
open import foundation.negation
open import foundation.universe-levels
open import foundation.weak-limited-principle-of-omniscience

open import foundation-core.identity-types

open import set-theory.increasing-binary-sequences
```

</details>

## Idea

We record relations between conditions on the
[increasing binary sequences](set-theory.increasing-binary-sequences.md) and the
[weak limited principle of omniscience](foundation.weak-limited-principle-of-omniscience.md)
(WLPO).

## Properties

### WLPO is equivalent to decidable equality on increasing binary sequences

```agda
abstract
  has-decidable-equality-ℕ∞↗-WLPO : WLPO → has-decidable-equality ℕ∞↗
  has-decidable-equality-ℕ∞↗-WLPO wlpo x y =
    map-coproduct
      ( eq-Eq-ℕ∞↗)
      ( _∘ Eq-eq-ℕ∞↗)
      ( wlpo
        ( λ n →
          Id-Decidable-Prop
            ( bool-Discrete-Type)
            ( sequence-ℕ∞↗ x n)
            ( sequence-ℕ∞↗ y n)))
```

```agda
abstract
  bool-WLPO-has-decidable-equality-ℕ∞↗ :
    has-decidable-equality ℕ∞↗ → bool-WLPO
  bool-WLPO-has-decidable-equality-ℕ∞↗ d f =
    map-coproduct
      ( λ p n →
        is-true-is-false-neg-bool
          ( all-false-eq-infinity-force-ℕ∞↗ (neg-bool ∘ f) p n))
      ( λ np q →
        np
          ( eq-Eq-ℕ∞↗
            ( Eq-infinity-force-ℕ∞↗-all-false
              ( neg-bool ∘ f)
              ( ap neg-bool ∘ q))))
      ( d (force-ℕ∞↗ (neg-bool ∘ f)) infinity-ℕ∞↗)

  WLPO-has-decidable-equality-ℕ∞↗ : has-decidable-equality ℕ∞↗ → WLPO
  WLPO-has-decidable-equality-ℕ∞↗ d =
    WLPO-bool-WLPO (bool-WLPO-has-decidable-equality-ℕ∞↗ d)
```

### If the increasing binary sequences embed into ℕ, then WLPO holds

```agda
WLPO-equiv-ℕ-ℕ∞↗ : (ℕ ≃ ℕ∞↗) → WLPO
WLPO-equiv-ℕ-ℕ∞↗ e =
  WLPO-has-decidable-equality-ℕ∞↗
    ( has-decidable-equality-equiv' e has-decidable-equality-ℕ)

WLPO-emb-ℕ∞↗-ℕ : (ℕ∞↗ ↪ ℕ) → WLPO
WLPO-emb-ℕ∞↗-ℕ e =
  WLPO-has-decidable-equality-ℕ∞↗
    ( has-decidable-equality-emb e has-decidable-equality-ℕ)
```
