# Unit fractions in the rational numbers types

```agda
{-# OPTIONS --lossy-unification #-}

module elementary-number-theory.unit-fractions-rational-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.archimedean-property-positive-rational-numbers
open import elementary-number-theory.inequality-integers
open import elementary-number-theory.inequality-rational-numbers
open import elementary-number-theory.integer-fractions
open import elementary-number-theory.integers
open import elementary-number-theory.multiplication-integer-fractions
open import elementary-number-theory.multiplication-integers
open import elementary-number-theory.multiplication-rational-numbers
open import elementary-number-theory.multiplicative-group-of-positive-rational-numbers
open import elementary-number-theory.multiplicative-inverses-positive-integer-fractions
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.nonzero-natural-numbers
open import elementary-number-theory.positive-integers
open import elementary-number-theory.positive-rational-numbers
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.strict-inequality-integers
open import elementary-number-theory.strict-inequality-rational-numbers

open import foundation.action-on-identifications-functions
open import foundation.binary-transport
open import foundation.dependent-pair-types
open import foundation.equality-cartesian-product-types
open import foundation.equality-dependent-pair-types
open import foundation.functoriality-dependent-pair-types
open import foundation.unit-type

open import foundation-core.coproduct-types
open import foundation-core.identity-types

open import group-theory.groups
```

</details>

## Idea

The {{#concept "unit fractions" WDID=Q255388 WD="unit fraction"}} are
[rational numbers](elementary-number-theory.rational-numbers.md) whose numerator
is 1 and whose denominator is a positive integer (or, equivalently, a positive
natural number).

## Definitions

### Reciprocals of nonzero natural numbers

```agda
positive-reciprocal-rational-ℕ⁺ : ℕ⁺ → ℚ⁺
positive-reciprocal-rational-ℕ⁺ n = inv-ℚ⁺ (positive-rational-ℕ⁺ n)

reciprocal-rational-ℕ⁺ : ℕ⁺ → ℚ
reciprocal-rational-ℕ⁺ n = rational-ℚ⁺ (positive-reciprocal-rational-ℕ⁺ n)

positive-reciprocal-rational-succ-ℕ : ℕ → ℚ⁺
positive-reciprocal-rational-succ-ℕ n =
  positive-reciprocal-rational-ℕ⁺ (succ-nonzero-ℕ' n)

reciprocal-rational-succ-ℕ : ℕ → ℚ
reciprocal-rational-succ-ℕ n =
  reciprocal-rational-ℕ⁺ (succ-nonzero-ℕ' n)
```

### If `m ≤ n`, the reciprocal of `n` is less than or equal to the reciprocal of `n`

```agda
opaque
  unfolding inv-ℚ⁺
  unfolding leq-ℚ-Prop

  leq-reciprocal-rational-ℕ⁺ :
    (m n : ℕ⁺) → leq-ℕ⁺ m n →
    leq-ℚ (reciprocal-rational-ℕ⁺ n) (reciprocal-rational-ℕ⁺ m)
  leq-reciprocal-rational-ℕ⁺ (m , pos-m) (n , pos-n) m≤n =
    binary-tr
      ( leq-ℤ)
      ( left-unit-law-mul-ℤ (int-ℕ m))
      ( left-unit-law-mul-ℤ (int-ℕ n))
      ( leq-int-ℕ m n m≤n)
```

### If `m < n`, the reciprocal of `n` is less than the reciprocal of `n`

```agda
opaque
  unfolding inv-ℚ⁺
  unfolding le-ℚ-Prop

  le-reciprocal-rational-ℕ⁺ :
    (m n : ℕ⁺) → le-ℕ⁺ m n →
    le-ℚ⁺
      ( positive-reciprocal-rational-ℕ⁺ n)
      ( positive-reciprocal-rational-ℕ⁺ m)
  le-reciprocal-rational-ℕ⁺ (m , pos-m) (n , pos-n) m<n =
    binary-tr
      ( le-ℤ)
      ( left-unit-law-mul-ℤ (int-ℕ m))
      ( left-unit-law-mul-ℤ (int-ℕ n))
      ( le-natural-le-ℤ m n m<n)
```

## Properties

### For every positive rational number, there is a smaller unit fraction

```agda
smaller-reciprocal-ℚ⁺ :
  (q : ℚ⁺) → Σ ℕ⁺ (λ n → le-ℚ⁺ (positive-reciprocal-rational-ℕ⁺ n) q)
smaller-reciprocal-ℚ⁺ q⁺@(q , _) =
  tot
    ( λ n⁺ 1<nq →
      binary-tr
        ( le-ℚ)
        ( right-unit-law-mul-ℚ _)
        ( ap
          ( rational-ℚ⁺)
          ( is-retraction-left-div-Group
            ( group-mul-ℚ⁺)
            ( positive-rational-ℕ⁺ n⁺)
            ( q⁺)))
        ( preserves-le-left-mul-ℚ⁺
          ( positive-reciprocal-rational-ℕ⁺ n⁺)
          ( one-ℚ)
          ( rational-ℚ⁺ (positive-rational-ℕ⁺ n⁺ *ℚ⁺ q⁺))
          ( 1<nq)))
    ( bound-archimedean-property-ℚ⁺ q⁺ one-ℚ⁺)
```

### For every `n : ℕ⁺`, `n * 1/n = 1`

```agda
{-
unit-fraction-is-left-inv-ℚ : (n : ℕ⁺) → mul-ℚ (reciprocal-rational-ℕ⁺ n) (rational-ℕ (nat-ℕ⁺ n)) ＝ one-ℚ
unit-fraction-is-left-inv-ℚ (n , n>0) = ap rational-fraction-ℤ (eq-pair refl {!   !}) ∙ (eq-ℚ-sim-fraction-ℤ (int-positive-ℤ (positive-int-ℕ⁺ (n , n>0)) , positive-int-ℕ⁺ (n , n>0)) one-fraction-ℤ (is-sim-one-fraction-ℤ (positive-int-ℕ⁺ (n , n>0))) ∙ {!   !})

unit-fraction-is-right-inv-ℚ : (n : ℕ⁺) → mul-ℚ (rational-ℕ (nat-ℕ⁺ n)) (reciprocal-rational-ℕ⁺ n) ＝ one-ℚ
unit-fraction-is-right-inv-ℚ (n , n>0) = {!   !}
-}
```
