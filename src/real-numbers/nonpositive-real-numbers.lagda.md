# Nonpositive real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.nonpositive-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.propositions
open import foundation.subtypes
open import foundation.universe-levels

open import real-numbers.dedekind-real-numbers
open import real-numbers.inequality-real-numbers
open import real-numbers.rational-real-numbers
```

</details>

## Idea

A [real number](real-numbers.dedekind-real-numbers.md) is
{{#concept "nonpositive" Disambiguation="real numbers" Agda=is-nonpositive-ℝ}}
if it is [less than or equal to](real-numbers.inequality-real-numbers.md)
[zero](real-numbers.rational-real-numbers.md).

## Definition

```agda
is-nonpositive-prop-ℝ : {l : Level} → ℝ l → Prop l
is-nonpositive-prop-ℝ x = leq-prop-ℝ x zero-ℝ

is-nonpositive-ℝ : {l : Level} → ℝ l → UU l
is-nonpositive-ℝ x = leq-ℝ x zero-ℝ

ℝ⁰⁻ : (l : Level) → UU (lsuc l)
ℝ⁰⁻ l = type-subtype (is-nonpositive-prop-ℝ {l})

real-ℝ⁰⁻ : {l : Level} → ℝ⁰⁻ l → ℝ l
real-ℝ⁰⁻ = pr1

is-nonpositive-real-ℝ⁰⁻ :
  {l : Level} (x : ℝ⁰⁻ l) → is-nonpositive-ℝ (real-ℝ⁰⁻ x)
is-nonpositive-real-ℝ⁰⁻ = pr2
```
