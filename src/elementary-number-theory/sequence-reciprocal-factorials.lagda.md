# The sequence of reciprocal of factorials of natural numbers

```agda
{-# OPTIONS --lossy-unification #-}

module elementary-number-theory.sequence-reciprocal-factorials where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.addition-rational-numbers
open import elementary-number-theory.archimedean-property-positive-rational-numbers
open import elementary-number-theory.binomial-coefficients
open import elementary-number-theory.difference-rational-numbers
open import elementary-number-theory.factorials
open import elementary-number-theory.inequality-integers
open import elementary-number-theory.inequality-rational-numbers
open import elementary-number-theory.integer-fractions
open import elementary-number-theory.integers
open import elementary-number-theory.multiplication-integer-fractions
open import elementary-number-theory.multiplication-integers
open import elementary-number-theory.multiplication-positive-rational-numbers
open import elementary-number-theory.multiplication-rational-numbers
open import elementary-number-theory.multiplicative-group-of-positive-rational-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.nonzero-natural-numbers
open import elementary-number-theory.positive-integers
open import elementary-number-theory.positive-rational-numbers
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.strict-inequality-integers
open import elementary-number-theory.strict-inequality-positive-rational-numbers
open import elementary-number-theory.strict-inequality-rational-numbers
open import elementary-number-theory.unit-fractions-rational-numbers

open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.binary-transport
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.identity-types
open import foundation.subtypes
open import foundation.transport-along-identifications
```

</details>

## Idea

The {{#concept "sequence of reciprocal of factorials" Agda=inv-factorial-ℕ}} is
the sequence `ℕ → ℚ` defined by `n ↦ 1/n!`.

## Definitions

### The sequence of inverses of factorials

```agda
positive-inv-factorial-ℕ : ℕ → ℚ⁺
positive-inv-factorial-ℕ =
  positive-reciprocal-rational-ℕ⁺ ∘ nonzero-factorial-ℕ

inv-factorial-ℕ : ℕ → ℚ
inv-factorial-ℕ = rational-ℚ⁺ ∘ positive-inv-factorial-ℕ
```

## Properties

### Computation rule with the binomial coefficients

```agda
-- abstract
--   binomial-coefficient-inv-factorial-formula-ℕ :
--     ( k l : ℕ) →
--     ( mul-ℚ
--       ( inv-factorial-ℕ (k +ℕ l))
--       ( rational-ℕ (binomial-coefficient-ℕ (k +ℕ l) k))) ＝
--     ( mul-ℚ
--       ( inv-factorial-ℕ k)
--       ( inv-factorial-ℕ l))
--   binomial-coefficient-inv-factorial-formula-ℕ k l =
--     {!!}
```
