# The floor of nonnegative rational numbers

```agda
{-# OPTIONS --lossy-unification #-}

module elementary-number-theory.floor-nonnegative-rational-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-rational-numbers
open import elementary-number-theory.additive-group-of-rational-numbers
open import elementary-number-theory.difference-rational-numbers
open import elementary-number-theory.distance-rational-numbers
open import elementary-number-theory.floor-nonnegative-integer-fractions
open import elementary-number-theory.inequality-rational-numbers
open import elementary-number-theory.integers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.nonnegative-integers
open import elementary-number-theory.nonnegative-rational-numbers
open import elementary-number-theory.nonpositive-rational-numbers
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.strict-inequality-rational-numbers

open import foundation.identity-types
open import foundation.transport-along-identifications
```

</details>

## Idea

The
{{#concept "floor" Disambiguation="of a nonnegative rational number" Agda=floor-ℚ⁰⁺}}
of a [nonnegative](elementary-number-theory.nonnegative-rational-numbers.md)
[rational number](elementary-number-theory.rational-numbers.md) `q` is the
[greatest](elementary-number-theory.inequality-integers.md)
[integer](elementary-number-theory.integers.md) `x` such that `rational-ℤ x` is
[less than or equal to](elementary-number-theory.inequality-rational-numbers.md)
`q`.

The constraint that `q` is nonnegative guarantees that `x` is
[nonnegative](elementary-number-theory.nonnegative-integers.md).

## Definition

```agda
module _
  (q : ℚ⁰⁺)
  where

  opaque
    nat-floor-ℚ⁰⁺ : ℕ
    nat-floor-ℚ⁰⁺ =
      nat-floor-is-nonnegative-fraction-ℤ
        ( fraction-ℚ⁰⁺ q)
        ( is-nonnegative-fraction-ℚ⁰⁺ q)

  floor-ℚ⁰⁺ : ℤ
  floor-ℚ⁰⁺ = int-ℕ nat-floor-ℚ⁰⁺

  rational-floor-ℚ⁰⁺ : ℚ
  rational-floor-ℚ⁰⁺ = rational-ℕ nat-floor-ℚ⁰⁺
```

## Properties

### The floor of a nonnegative rational number is nonnegative

```agda
module _
  (q : ℚ⁰⁺)
  where

  abstract
    is-nonnegative-floor-ℚ⁰⁺ : is-nonnegative-ℤ (floor-ℚ⁰⁺ q)
    is-nonnegative-floor-ℚ⁰⁺ = is-nonnegative-int-ℕ (nat-floor-ℚ⁰⁺ q)

  nonnegative-floor-ℚ⁰⁺ : nonnegative-ℤ
  nonnegative-floor-ℚ⁰⁺ = nonnegative-int-ℕ (nat-floor-ℚ⁰⁺ q)
```

### The floor of a nonnegative rational number is less than or equal to the rational number

```agda
module _
  (q : ℚ⁰⁺)
  where

  abstract opaque
    unfolding leq-ℚ-Prop nat-floor-ℚ⁰⁺

    leq-floor-ℚ⁰⁺ : leq-ℚ (rational-ℤ (floor-ℚ⁰⁺ q)) (rational-ℚ⁰⁺ q)
    leq-floor-ℚ⁰⁺ =
      leq-floor-is-nonnegative-fraction-ℤ
        ( fraction-ℚ⁰⁺ q)
        ( is-nonnegative-fraction-ℚ⁰⁺ q)
```

### A nonnegative rational number is less than the successor of its floor

```agda
module _
  (q : ℚ⁰⁺)
  where

  abstract opaque
    unfolding le-ℚ-Prop nat-floor-ℚ⁰⁺

    le-succ-floor-ℚ⁰⁺ :
      le-ℚ (rational-ℚ⁰⁺ q) (rational-ℤ (succ-ℤ (floor-ℚ⁰⁺ q)))
    le-succ-floor-ℚ⁰⁺ =
      le-succ-floor-is-nonnegative-fraction-ℤ
        ( fraction-ℚ⁰⁺ q)
        ( is-nonnegative-fraction-ℚ⁰⁺ q)

    le-succ-rational-floor-ℚ⁰⁺ :
      le-ℚ (rational-ℚ⁰⁺ q) (succ-ℚ (rational-floor-ℚ⁰⁺ q))
    le-succ-rational-floor-ℚ⁰⁺ =
      inv-tr
        ( le-ℚ (rational-ℚ⁰⁺ q))
        ( succ-rational-ℤ (floor-ℚ⁰⁺ q))
        ( le-succ-floor-ℚ⁰⁺)
```

### The distance between a rational number and its floor is less than 1

```agda
module _
  (q : ℚ⁰⁺)
  where

  abstract
    le-one-dist-floor-ℚ⁰⁺ :
      le-ℚ
        ( rational-dist-ℚ (rational-ℚ⁰⁺ q) (rational-floor-ℚ⁰⁺ q))
        ( one-ℚ)
    le-one-dist-floor-ℚ⁰⁺ =
      le-dist-le-diff-ℚ
        ( rational-ℚ⁰⁺ q)
        ( rational-floor-ℚ⁰⁺ q)
        ( one-ℚ)
        ( tr
          ( le-ℚ _)
          ( ( ap-diff-ℚ (inv (succ-rational-ℤ _)) refl) ∙
            ( is-retraction-diff-ℚ (rational-floor-ℚ⁰⁺ q) one-ℚ))
          ( preserves-le-left-add-ℚ
            ( neg-ℚ (rational-floor-ℚ⁰⁺ q))
            ( rational-ℚ⁰⁺ q)
            ( rational-ℤ (succ-ℤ (floor-ℚ⁰⁺ q)))
            ( le-succ-floor-ℚ⁰⁺ q)))
        ( concatenate-leq-le-ℚ
          ( rational-floor-ℚ⁰⁺ q -ℚ rational-ℚ⁰⁺ q)
          ( zero-ℚ)
          ( one-ℚ)
          ( leq-zero-is-nonpositive-ℚ
            ( is-nonpositive-diff-leq-ℚ (leq-floor-ℚ⁰⁺ q)))
          ( le-zero-one-ℚ))
```
