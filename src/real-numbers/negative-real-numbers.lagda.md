# Negative real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.negative-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.negative-rational-numbers

open import foundation.dependent-pair-types
open import foundation.existential-quantification
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.propositions
open import foundation.subtypes
open import foundation.universe-levels

open import real-numbers.dedekind-real-numbers
open import real-numbers.rational-real-numbers
open import real-numbers.similarity-real-numbers
open import real-numbers.strict-inequality-real-numbers
```

</details>

## Idea

A [real number](real-numbers.dedekind-real-numbers.md) is
{{#concept "negative" Disambiguation="real number" Agda=is-negative-ℝ}} if it is
[strictly less than](real-numbers.strict-inequality-real-numbers.md) zero.

## Definition

```agda
is-negative-prop-ℝ : {l : Level} (x : ℝ l) → Prop l
is-negative-prop-ℝ x = le-prop-ℝ x zero-ℝ

is-negative-ℝ : {l : Level} (x : ℝ l) → UU l
is-negative-ℝ x = le-ℝ x zero-ℝ

negative-ℝ : (l : Level) → UU (lsuc l)
negative-ℝ l = type-subtype (is-negative-prop-ℝ {l})

ℝ⁻ : (l : Level) → UU (lsuc l)
ℝ⁻ = negative-ℝ

real-ℝ⁻ : {l : Level} → ℝ⁻ l → ℝ l
real-ℝ⁻ = inclusion-subtype is-negative-prop-ℝ
```

## Properties

### Characterization of equality

```agda
abstract
  eq-ℝ⁻ : {l : Level} (x y : ℝ⁻ l) → (real-ℝ⁻ x ＝ real-ℝ⁻ y) → x ＝ y
  eq-ℝ⁻ _ _ = eq-type-subtype is-negative-prop-ℝ
```

### A real number is negative if and only if a negative rational number is in its upper cut

```agda
module _
  {l : Level} (x : ℝ l)
  where

  opaque
    unfolding le-ℝ real-ℚ

    exists-ℚ⁻-in-upper-cut-is-negative-ℝ :
      is-negative-ℝ x → exists ℚ⁻ (λ p → upper-cut-ℝ x (rational-ℚ⁻ p))
    exists-ℚ⁻-in-upper-cut-is-negative-ℝ =
      elim-exists
        ( ∃ ℚ⁻ (λ p → upper-cut-ℝ x (rational-ℚ⁻ p)))
        ( λ p (x<p , p<0) → intro-exists (p , is-negative-le-zero-ℚ p<0) x<p)

    is-negative-exists-ℚ⁻-in-upper-cut-ℝ :
      exists ℚ⁻ (λ p → upper-cut-ℝ x (rational-ℚ⁻ p)) → is-negative-ℝ x
    is-negative-exists-ℚ⁻-in-upper-cut-ℝ =
      elim-exists
        ( is-negative-prop-ℝ x)
        ( λ (p , is-neg-p) x<p →
          intro-exists p (x<p , le-zero-is-negative-ℚ is-neg-p))

    is-negative-iff-exists-ℚ⁻-in-upper-cut-ℝ :
      is-negative-ℝ x ↔ exists ℚ⁻ (λ p → upper-cut-ℝ x (rational-ℚ⁻ p))
    is-negative-iff-exists-ℚ⁻-in-upper-cut-ℝ =
      ( exists-ℚ⁻-in-upper-cut-is-negative-ℝ ,
        is-negative-exists-ℚ⁻-in-upper-cut-ℝ)
```

### Being nonnegative is preserved by similarity

```agda
abstract
  is-negative-sim-ℝ :
    {l1 l2 : Level} {x : ℝ l1} {y : ℝ l2} →
    sim-ℝ x y → is-negative-ℝ x → is-negative-ℝ y
  is-negative-sim-ℝ = preserves-le-left-sim-ℝ _ _ _
```
