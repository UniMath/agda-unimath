# Strict lower bounds on increasing binary sequences

```agda
module set-theory.strict-lower-bounds-increasing-binary-sequences where
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
```

</details>

## Idea

An [increasing binary sequence](set-theory.increasing-binary-sequences.md) `x`
is
{{#concept "strictly bounded below" Disambiguation="element of the type of increasing binary sequences by natural number" Agda=is-strictly-bounded-below-ℕ∞↗}}
by a [natural number](elementary-number-theory.natural-numbers.md) `n : ℕ` if
`xₙ` is false.

## Definitions

### Strict finite boundedness below of increasing binary sequences

```agda
is-strictly-bounded-below-decidable-prop-ℕ∞↗ :
  ℕ → ℕ∞↗ → Decidable-Prop lzero
is-strictly-bounded-below-decidable-prop-ℕ∞↗ n x =
  is-false-Decidable-Prop (sequence-ℕ∞↗ x n)

is-strictly-bounded-below-prop-ℕ∞↗ : ℕ → ℕ∞↗ → Prop lzero
is-strictly-bounded-below-prop-ℕ∞↗ n x =
  prop-Decidable-Prop
    ( is-strictly-bounded-below-decidable-prop-ℕ∞↗ n x)

is-strictly-bounded-below-ℕ∞↗ : ℕ → ℕ∞↗ → UU lzero
is-strictly-bounded-below-ℕ∞↗ x n =
  type-Decidable-Prop
    ( is-strictly-bounded-below-decidable-prop-ℕ∞↗ x n)

is-prop-is-strictly-bounded-below-ℕ∞↗ :
  (n : ℕ) (x : ℕ∞↗) →
  is-prop (is-strictly-bounded-below-ℕ∞↗ n x)
is-prop-is-strictly-bounded-below-ℕ∞↗ n x =
  is-prop-type-Decidable-Prop
    ( is-strictly-bounded-below-decidable-prop-ℕ∞↗ n x)

is-decidable-is-strictly-bounded-below-ℕ∞↗ :
  (n : ℕ) (x : ℕ∞↗) →
  is-decidable (is-strictly-bounded-below-ℕ∞↗ n x)
is-decidable-is-strictly-bounded-below-ℕ∞↗ n x =
  is-decidable-Decidable-Prop
    ( is-strictly-bounded-below-decidable-prop-ℕ∞↗ n x)
```

## Properties

### If an increasing binary sequence is strictly bounded below by `𝑛+1` then it strictly bounded below by `𝑛`

```agda
is-strictly-bounded-below-is-strictly-bounded-below-succ-ℕ∞↗ :
  (x : ℕ∞↗) (n : ℕ) →
  is-strictly-bounded-below-ℕ∞↗ (succ-ℕ n) x →
  is-strictly-bounded-below-ℕ∞↗ n x
is-strictly-bounded-below-is-strictly-bounded-below-succ-ℕ∞↗ x n =
  is-false-is-false-leq-bool (is-increasing-sequence-ℕ∞↗ x n)
```
