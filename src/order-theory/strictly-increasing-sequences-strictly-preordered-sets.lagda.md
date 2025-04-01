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
open import foundation.sequences
open import foundation.universe-levels

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
[strict ordering on the natural numbers](elementary-number-theory.strict-inequality-natural-numbers.md)

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
      ℕ-Strict-Preordered-Set
      A
      u

  is-strictly-increasing-sequence-Strictly-Preordered-Set : UU l2
  is-strictly-increasing-sequence-Strictly-Preordered-Set =
    preserves-strict-order-map-Strictly-Preordered-Set
      ℕ-Strict-Preordered-Set
      A
      u

  is-prop-is-strictly-increasing-sequence-Strictly-Preordered-Set :
    is-prop is-strictly-increasing-sequence-Strictly-Preordered-Set
  is-prop-is-strictly-increasing-sequence-Strictly-Preordered-Set =
    is-prop-preserves-strict-order-map-Strictly-Preordered-Set
      ℕ-Strict-Preordered-Set
      A
      u
```
