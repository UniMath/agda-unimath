# The sine power series on the real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module analysis.sine-power-series-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import analysis.absolute-convergence-series-real-numbers
open import analysis.comparison-test-series-real-numbers
open import analysis.exponential-power-series-real-numbers
open import analysis.power-series-at-zero-real-numbers
open import analysis.series-real-numbers

open import elementary-number-theory.factorials
open import elementary-number-theory.modular-arithmetic
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.unit-fractions-rational-numbers

open import foundation.action-on-identifications-functions
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.transport-along-identifications
open import foundation.unit-type
open import foundation.universe-levels

open import lists.sequences

open import real-numbers.absolute-value-real-numbers
open import real-numbers.dedekind-real-numbers
open import real-numbers.inequality-real-numbers
open import real-numbers.multiplication-real-numbers
open import real-numbers.negation-real-numbers
open import real-numbers.powers-real-numbers
open import real-numbers.raising-universe-levels-real-numbers
open import real-numbers.rational-real-numbers
open import real-numbers.similarity-real-numbers

open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

The [sine function](analysis.sine-function-real-numbers.md) is defined by the
power series

$$
∑_{n=0}^∞ (-1)^{2n+1} \frac{x^{2n+1}}{(2n+1)!}
$$

This file defines the power series and its properties.

## Definition

```agda
coefficient-sin-power-series-at-zero-ℝ : (l : Level) → sequence (ℝ l)
coefficient-sin-power-series-at-zero-ℝ l n =
  let
    case : ℤ-Mod 4 → ℝ l
    case =
      λ {
        (inr star) →
          neg-ℝ
            ( raise-real-ℚ l (reciprocal-rational-ℕ⁺ (nonzero-factorial-ℕ n))) ;
        (inl (inr star)) → raise-ℝ l zero-ℝ ;
        (inl (inl (inr star))) →
          raise-real-ℚ l (reciprocal-rational-ℕ⁺ (nonzero-factorial-ℕ n)) ;
        (inl (inl (inl (inr star)))) →
          raise-ℝ l zero-ℝ
      }
  in
    case (mod-ℕ 4 n)

sin-power-series-at-zero-ℝ : (l : Level) → power-series-at-zero-ℝ l
sin-power-series-at-zero-ℝ l =
  power-series-at-zero-coefficients-ℝ (coefficient-sin-power-series-at-zero-ℝ l)

term-at-point-sin-power-series-at-zero-ℝ : {l : Level} → ℝ l → sequence (ℝ l)
term-at-point-sin-power-series-at-zero-ℝ {l} =
  term-at-point-power-series-at-zero-ℝ (sin-power-series-at-zero-ℝ l)
```

## Properties

### The sine power series absolutely converges everywhere

```agda
abstract
  leq-abs-term-at-point-sin-exp-power-series-at-zero-ℝ :
    {l : Level} (x : ℝ l) (n : ℕ) →
    leq-ℝ
      ( abs-ℝ (term-at-point-sin-power-series-at-zero-ℝ x n))
      ( abs-ℝ (term-at-point-exp-power-series-at-zero-ℝ x n))
  leq-abs-term-at-point-sin-exp-power-series-at-zero-ℝ {l} x n
    with mod-ℕ 4 n
  ... | inl (inr star) =
    preserves-leq-left-sim-ℝ
      ( similarity-reasoning-ℝ
        zero-ℝ
        ~ℝ zero-ℝ *ℝ abs-ℝ (power-ℝ n x)
          by symmetric-sim-ℝ (left-zero-law-mul-ℝ _)
        ~ℝ abs-ℝ zero-ℝ *ℝ abs-ℝ (power-ℝ n x)
          by sim-eq-ℝ (ap-mul-ℝ (inv abs-zero-ℝ) refl)
        ~ℝ abs-ℝ (raise-ℝ l zero-ℝ) *ℝ abs-ℝ (power-ℝ n x)
          by
            preserves-sim-right-mul-ℝ _ _ _
              ( preserves-sim-abs-ℝ (sim-raise-ℝ l zero-ℝ))
        ~ℝ abs-ℝ (raise-ℝ l zero-ℝ *ℝ power-ℝ n x)
          by sim-eq-ℝ (inv (abs-mul-ℝ _ _)))
      ( is-nonnegative-abs-ℝ _)
  ... | inr star =
    let
      1/n! = raise-real-ℚ l (reciprocal-rational-ℕ⁺ (nonzero-factorial-ℕ n))
    in
      leq-eq-ℝ
        ( equational-reasoning
          abs-ℝ (neg-ℝ 1/n! *ℝ power-ℝ n x)
          ＝ abs-ℝ (neg-ℝ (1/n! *ℝ power-ℝ n x))
            by ap abs-ℝ (left-negative-law-mul-ℝ _ _)
          ＝ abs-ℝ (1/n! *ℝ power-ℝ n x)
            by abs-neg-ℝ _)
  ... | inl (inl (inl (inr star))) =
    preserves-leq-left-sim-ℝ
      ( similarity-reasoning-ℝ
        zero-ℝ
        ~ℝ zero-ℝ *ℝ abs-ℝ (power-ℝ n x)
          by symmetric-sim-ℝ (left-zero-law-mul-ℝ _)
        ~ℝ abs-ℝ zero-ℝ *ℝ abs-ℝ (power-ℝ n x)
          by sim-eq-ℝ (ap-mul-ℝ (inv abs-zero-ℝ) refl)
        ~ℝ abs-ℝ (raise-ℝ l zero-ℝ) *ℝ abs-ℝ (power-ℝ n x)
          by
            preserves-sim-right-mul-ℝ _ _ _
              ( preserves-sim-abs-ℝ (sim-raise-ℝ l zero-ℝ))
        ~ℝ abs-ℝ (raise-ℝ l zero-ℝ *ℝ power-ℝ n x)
          by sim-eq-ℝ (inv (abs-mul-ℝ _ _)))
      ( is-nonnegative-abs-ℝ _)
  ... | inl (inl (inr star)) =
    refl-leq-ℝ _

  is-absolutely-convergent-everywhere-sin-power-series-at-zero-ℝ :
    {l : Level} (x : ℝ l) →
    is-absolutely-convergent-at-point-power-series-at-zero-ℝ
      ( sin-power-series-at-zero-ℝ l)
      ( x)
  is-absolutely-convergent-everywhere-sin-power-series-at-zero-ℝ {l} x =
    is-convergent-is-nonnegative-is-bounded-by-convergent-series-ℝ
      ( map-abs-series-ℝ
        ( compute-series-at-point-power-series-at-zero-ℝ
          ( sin-power-series-at-zero-ℝ l)
          ( x)))
      ( map-abs-series-ℝ
        ( compute-series-at-point-power-series-at-zero-ℝ
          ( exp-power-series-at-zero-ℝ l)
          ( x)) ,
        is-absolutely-convergent-everywhere-exp-power-series-at-zero-ℝ x)
      ( λ n → is-nonnegative-abs-ℝ _)
      ( leq-abs-term-at-point-sin-exp-power-series-at-zero-ℝ x)

  is-convergent-everywhere-sin-power-series-at-zero-ℝ :
    (l : Level) →
    is-convergent-everywhere-power-series-at-zero-ℝ
      ( sin-power-series-at-zero-ℝ l)
  is-convergent-everywhere-sin-power-series-at-zero-ℝ l x =
    is-convergent-is-absolutely-convergent-series-ℝ
      ( compute-series-at-point-power-series-at-zero-ℝ
        ( sin-power-series-at-zero-ℝ l)
        ( x))
      ( is-absolutely-convergent-everywhere-sin-power-series-at-zero-ℝ x)
```

### The convergent power series of the sinine function

```agda
sin-convergent-everywhere-power-series-ℝ :
  (l : Level) → convergent-everywhere-power-series-at-zero-ℝ l
sin-convergent-everywhere-power-series-ℝ l =
  ( sin-power-series-at-zero-ℝ l ,
    is-convergent-everywhere-sin-power-series-at-zero-ℝ l)
```
