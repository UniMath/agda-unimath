# Positive elements in the type of increasing binary sequences

```agda
module set-theory.positive-elements-increasing-binary-sequences where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.booleans
open import foundation.constant-maps
open import foundation.decidable-propositions
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.equality-dependent-pair-types
open import foundation.function-types
open import foundation.homotopies
open import foundation.inequality-booleans
open import foundation.inhabited-types
open import foundation.negation
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.universe-levels

open import foundation-core.identity-types

open import set-theory.increasing-binary-sequences
open import set-theory.strict-lower-bounds-increasing-binary-sequences
```

</details>

## Idea

An [increasing binary sequence](set-theory.increasing-binary-sequences.md) `x`
is
{{#concept "positive" Disambiguation="element of the type of increasing binary sequences" Agda=is-positive-ℕ∞↗ Agda=ℕ∞↗₊}}
if `x₀` is false.

## Definitions

### The predicate on increasing binary sequences of being positive

```agda
is-positive-ℕ∞↗ : ℕ∞↗ → UU lzero
is-positive-ℕ∞↗ = is-strictly-bounded-below-ℕ∞↗ 0

abstract
  is-prop-is-positive-ℕ∞↗ :
    (x : ℕ∞↗) → is-prop (is-positive-ℕ∞↗ x)
  is-prop-is-positive-ℕ∞↗ =
    is-prop-is-strictly-bounded-below-ℕ∞↗ 0

is-positive-prop-ℕ∞↗ : ℕ∞↗ → Prop lzero
is-positive-prop-ℕ∞↗ =
  is-strictly-bounded-below-prop-ℕ∞↗ 0
```

### The type of positive increasing binary sequences

```agda
positive-ℕ∞↗ : UU lzero
positive-ℕ∞↗ = Σ ℕ∞↗ is-positive-ℕ∞↗

ℕ∞↗₊ : UU lzero
ℕ∞↗₊ = positive-ℕ∞↗
```

## Properties

### If an increasing binary sequence is strictly bounded below, then it is positive

```agda
is-positive-is-strictly-bounded-below-ℕ∞↗ :
  (x : ℕ∞↗) (n : ℕ) →
  is-strictly-bounded-below-ℕ∞↗ n x → is-positive-ℕ∞↗ x
is-positive-is-strictly-bounded-below-ℕ∞↗ x 0 p = p
is-positive-is-strictly-bounded-below-ℕ∞↗ x (succ-ℕ n) p =
  is-positive-is-strictly-bounded-below-ℕ∞↗ x n
    ( is-strictly-bounded-below-is-strictly-bounded-below-succ-ℕ∞↗ x n p)
```
