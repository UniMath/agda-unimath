# Strictly increasing sequences in strictly preordered sets

```agda
module order-theory.strictly-increasing-sequences-strictly-preordered-sets where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.decidable-total-order-natural-numbers
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.strict-inequality-natural-numbers

open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.universe-levels

open import lists.sequences

open import order-theory.sequences-strictly-preordered-sets
open import order-theory.strict-order-preserving-maps
open import order-theory.strictly-preordered-sets
```

</details>

## Idea

A
[sequence in a strictly preordered set](order-theory.sequences-strictly-preordered-sets.md)
is called
{{#concept "strictly increasing" Disambiguation="sequence in a strictly preordered set}}
if it [preserves](order-theory.strict-order-preserving-maps.md) the
[strict ordering on the natural numbers](elementary-number-theory.strict-inequality-natural-numbers.md).

## Definitions

### Strictly increasing sequences in strictly preordered sets

```agda
module _
  {l1 l2 : Level} (A : Strictly-Preordered-Set l1 l2)
  (u : type-sequence-Strictly-Preordered-Set A)
  where

  is-strictly-increasing-prop-sequence-Strictly-Preordered-Set : Prop l2
  is-strictly-increasing-prop-sequence-Strictly-Preordered-Set =
    preserves-strict-order-prop-map-Strictly-Preordered-Set
      strictly-preordered-set-ℕ
      A
      u

  is-strictly-increasing-sequence-Strictly-Preordered-Set : UU l2
  is-strictly-increasing-sequence-Strictly-Preordered-Set =
    preserves-strict-order-map-Strictly-Preordered-Set
      strictly-preordered-set-ℕ
      A
      u

  is-prop-is-strictly-increasing-sequence-Strictly-Preordered-Set :
    is-prop is-strictly-increasing-sequence-Strictly-Preordered-Set
  is-prop-is-strictly-increasing-sequence-Strictly-Preordered-Set =
    is-prop-preserves-strict-order-map-Strictly-Preordered-Set
      strictly-preordered-set-ℕ
      A
      u
```

## Properties

### A sequence `u` in a strictly preordered set is strictly increasing if and only if `uₙ < uₙ₊₁` for all `n : ℕ`

```agda
module _
  {l1 l2 : Level} (A : Strictly-Preordered-Set l1 l2)
  where

  is-strictly-increasing-le-succ-sequence-Strictly-Preordered-Set :
    (u : type-sequence-Strictly-Preordered-Set A) →
    ((n : ℕ) → le-Strictly-Preordered-Set A (u n) (u (succ-ℕ n))) →
    is-strictly-increasing-sequence-Strictly-Preordered-Set A u
  is-strictly-increasing-le-succ-sequence-Strictly-Preordered-Set
    u H zero-ℕ (succ-ℕ zero-ℕ) I = H zero-ℕ
  is-strictly-increasing-le-succ-sequence-Strictly-Preordered-Set
    u H zero-ℕ (succ-ℕ (succ-ℕ n)) I =
      is-transitive-le-Strictly-Preordered-Set A
        ( u zero-ℕ)
        ( u (succ-ℕ n))
        ( u (succ-ℕ (succ-ℕ n)))
        ( H (succ-ℕ n))
        ( is-strictly-increasing-le-succ-sequence-Strictly-Preordered-Set
          ( u)
          ( H)
          ( zero-ℕ)
          ( succ-ℕ n)
          ( I))
  is-strictly-increasing-le-succ-sequence-Strictly-Preordered-Set
    u H (succ-ℕ m) (succ-ℕ n) I =
      is-strictly-increasing-le-succ-sequence-Strictly-Preordered-Set
        ( u ∘ succ-ℕ)
        ( H ∘ succ-ℕ)
        ( m)
        ( n)
        ( I)

  le-succ-is-strictly-increasing-sequence-Strictly-Preordered-Set :
    (u : type-sequence-Strictly-Preordered-Set A) →
    is-strictly-increasing-sequence-Strictly-Preordered-Set A u →
    ((n : ℕ) → le-Strictly-Preordered-Set A (u n) (u (succ-ℕ n)))
  le-succ-is-strictly-increasing-sequence-Strictly-Preordered-Set
    u H n = H n (succ-ℕ n) (succ-le-ℕ n)
```
