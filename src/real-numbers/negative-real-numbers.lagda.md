# Negative real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.negative-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import foundation.identity-types
open import foundation.propositions
open import foundation.subtypes
open import foundation.universe-levels

open import real-numbers.dedekind-real-numbers
open import real-numbers.rational-real-numbers
open import real-numbers.strict-inequality-real-numbers
```

</details>

## Idea

A [real number](real-numbers.dedekind-real-numbers.md) is
{{#concept "negative" Disambiguation="real number" Agda=is-positive-ℝ}} if it is
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
  eq-ℝ⁻ : {l : Level} → (x y : ℝ⁻ l) → (real-ℝ⁻ x ＝ real-ℝ⁻ y) → x ＝ y
  eq-ℝ⁻ _ _ = eq-type-subtype is-negative-prop-ℝ
```
