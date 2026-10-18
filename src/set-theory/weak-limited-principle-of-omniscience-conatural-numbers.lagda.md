# The weak limited principle of omniscience and the conatural numbers

```agda
{-# OPTIONS --guardedness #-}

module set-theory.weak-limited-principle-of-omniscience-conatural-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.conatural-numbers
open import elementary-number-theory.equality-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.decidable-equality
open import foundation.embeddings
open import foundation.equivalences
open import foundation.weak-limited-principle-of-omniscience

open import set-theory.equivalence-conatural-numbers-increasing-binary-sequences
open import set-theory.weak-limited-principle-of-omniscience-increasing-binary-sequences
```

</details>

## Idea

We record relations between conditions on the
[conatural numbers](elementary-number-theory.conatural-numbers.md) and the
[weak limited principle of omniscience](foundation.weak-limited-principle-of-omniscience.md)
(WLPO).

## Properties

### WLPO is equivalent to decidable equality on the conatural numbers

```agda
has-decidable-equality-ℕ∞-WLPO : WLPO → has-decidable-equality ℕ∞
has-decidable-equality-ℕ∞-WLPO wlpo =
  has-decidable-equality-equiv'
    ( equiv-conatural-number-ℕ∞↗)
    ( has-decidable-equality-ℕ∞↗-WLPO wlpo)

WLPO-has-decidable-equality-ℕ∞ : has-decidable-equality ℕ∞ → WLPO
WLPO-has-decidable-equality-ℕ∞ d =
  WLPO-has-decidable-equality-ℕ∞↗
    ( has-decidable-equality-equiv
      ( equiv-conatural-number-ℕ∞↗)
      ( d))
```

### If the conatural numbers embed into ℕ, then WLPO holds

```agda
WLPO-equiv-ℕ-ℕ∞ : (ℕ ≃ ℕ∞) → WLPO
WLPO-equiv-ℕ-ℕ∞ e =
  WLPO-has-decidable-equality-ℕ∞
    ( has-decidable-equality-equiv' e has-decidable-equality-ℕ)

WLPO-emb-ℕ∞-ℕ : (ℕ∞ ↪ ℕ) → WLPO
WLPO-emb-ℕ∞-ℕ e =
  WLPO-has-decidable-equality-ℕ∞
    ( has-decidable-equality-emb
      ( e)
      ( has-decidable-equality-ℕ))
```
