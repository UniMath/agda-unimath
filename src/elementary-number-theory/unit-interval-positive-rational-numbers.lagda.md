# The unit interval of positive rational numbers

```agda
{-# OPTIONS --lossy-unification #-}

module elementary-number-theory.unit-interval-positive-rational-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.decidable-total-order-rational-numbers
open import elementary-number-theory.inequality-rational-numbers
open import elementary-number-theory.maximum-rational-numbers
open import elementary-number-theory.minimum-rational-numbers
open import elementary-number-theory.multiplication-rational-numbers
open import elementary-number-theory.negative-rational-numbers
open import elementary-number-theory.positive-rational-numbers
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.strict-inequality-rational-numbers

open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.binary-transport
open import foundation.conjunction
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.universe-levels
```

</details>

## Idea

The
{{#concept "unit interval" Disambiguation="of positive rational numbers" Agda=unit-interval-ℚ⁺}}
is the subset of the
[positive rational numbers](elementary-number-theory.positive-rational-numbers.md)
lesser than 1.

## Definitions

### The unit interval of positive rational numbers

```agda
subtype-unit-interval-ℚ⁺ : subtype lzero ℚ⁺
subtype-unit-interval-ℚ⁺ x = le-prop-ℚ⁺ x one-ℚ⁺

unit-interval-ℚ⁺ : UU lzero
unit-interval-ℚ⁺ = type-subtype subtype-unit-interval-ℚ⁺

value-unit-interval-ℚ⁺ : unit-interval-ℚ⁺ → ℚ⁺
value-unit-interval-ℚ⁺ x = pr1 x

le-unit-value-unit-interval-ℚ⁺ :
  (x : unit-interval-ℚ⁺) → le-ℚ⁺ (value-unit-interval-ℚ⁺ x) one-ℚ⁺
le-unit-value-unit-interval-ℚ⁺ x = pr2 x
```

## Properties

TODO
