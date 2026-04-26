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
  {l1 l2 : Level} (A : Strict-Preorder l1 l2)
  (u : type-sequence-Strict-Preorder A)
  where

  is-strictly-increasing-prop-sequence-Strict-Preorder : Prop l2
  is-strictly-increasing-prop-sequence-Strict-Preorder =
    preserves-strict-order-prop-map-Strict-Preorder
      strictly-preordered-set-ℕ
      A
      u

  is-strictly-increasing-sequence-Strict-Preorder : UU l2
  is-strictly-increasing-sequence-Strict-Preorder =
    preserves-strict-order-map-Strict-Preorder
      strictly-preordered-set-ℕ
      A
      u

  is-prop-is-strictly-increasing-sequence-Strict-Preorder :
    is-prop is-strictly-increasing-sequence-Strict-Preorder
  is-prop-is-strictly-increasing-sequence-Strict-Preorder =
    is-prop-preserves-strict-order-map-Strict-Preorder
      strictly-preordered-set-ℕ
      A
      u
```

## Properties

### A sequence `u` in a strictly preordered set is strictly increasing if and only if `uₙ < uₙ₊₁` for all `n : ℕ`

```agda
module _
  {l1 l2 : Level} (A : Strict-Preorder l1 l2)
  where

  is-strictly-increasing-le-succ-sequence-Strict-Preorder :
    (u : type-sequence-Strict-Preorder A) →
    ((n : ℕ) → le-Strict-Preorder A (u n) (u (succ-ℕ n))) →
    is-strictly-increasing-sequence-Strict-Preorder A u
  is-strictly-increasing-le-succ-sequence-Strict-Preorder
    u H zero-ℕ (succ-ℕ zero-ℕ) I = H zero-ℕ
  is-strictly-increasing-le-succ-sequence-Strict-Preorder
    u H zero-ℕ (succ-ℕ (succ-ℕ n)) I =
      is-transitive-le-Strict-Preorder A
        ( u zero-ℕ)
        ( u (succ-ℕ n))
        ( u (succ-ℕ (succ-ℕ n)))
        ( H (succ-ℕ n))
        ( is-strictly-increasing-le-succ-sequence-Strict-Preorder
          ( u)
          ( H)
          ( zero-ℕ)
          ( succ-ℕ n)
          ( I))
  is-strictly-increasing-le-succ-sequence-Strict-Preorder
    u H (succ-ℕ m) (succ-ℕ n) I =
      is-strictly-increasing-le-succ-sequence-Strict-Preorder
        ( u ∘ succ-ℕ)
        ( H ∘ succ-ℕ)
        ( m)
        ( n)
        ( I)

  le-succ-is-strictly-increasing-sequence-Strict-Preorder :
    (u : type-sequence-Strict-Preorder A) →
    is-strictly-increasing-sequence-Strict-Preorder A u →
    ((n : ℕ) → le-Strict-Preorder A (u n) (u (succ-ℕ n)))
  le-succ-is-strictly-increasing-sequence-Strict-Preorder
    u H n = H n (succ-ℕ n) (succ-le-ℕ n)
```
