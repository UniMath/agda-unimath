# Nonzero real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.nonzero-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.disjunction
open import foundation.identity-types
open import foundation.propositions
open import foundation.subtypes
open import foundation.universe-levels

open import real-numbers.apartness-real-numbers
open import real-numbers.dedekind-real-numbers
open import real-numbers.negative-real-numbers
open import real-numbers.positive-real-numbers
open import real-numbers.rational-real-numbers
```

</details>

## Idea

A [real number](real-numbers.dedekind-real-numbers.md) is
{{#concept "nonzero" Disambiguation="Dedekind real numbers" Agda=is-nonzero-ℝ}}
if it is [apart](real-numbers.apartness-real-numbers.md) from zero, or
equivalently if it is [negative](real-numbers.negative-real-numbers.md)
[or](foundation.disjunction.md)
[positive](real-numbers.positive-real-numbers.md).

## Definition

```agda
is-nonzero-prop-ℝ : {l : Level} → ℝ l → Prop l
is-nonzero-prop-ℝ x = apart-prop-ℝ x zero-ℝ

is-nonzero-ℝ : {l : Level} → ℝ l → UU l
is-nonzero-ℝ x = type-Prop (is-nonzero-prop-ℝ x)

nonzero-ℝ : (l : Level) → UU (lsuc l)
nonzero-ℝ l = type-subtype (is-nonzero-prop-ℝ {l})

real-nonzero-ℝ : {l : Level} → nonzero-ℝ l → ℝ l
real-nonzero-ℝ = inclusion-subtype is-nonzero-prop-ℝ

is-nonzero-real-nonzero-ℝ :
  {l : Level} (x : nonzero-ℝ l) → is-nonzero-ℝ (real-nonzero-ℝ x)
is-nonzero-real-nonzero-ℝ = pr2
```

## Properties

### Positive real numbers are nonzero

```agda
is-nonzero-is-positive-ℝ :
  {l : Level} {x : ℝ l} → is-positive-ℝ x → is-nonzero-ℝ x
is-nonzero-is-positive-ℝ = inr-disjunction

nonzero-ℝ⁺ : {l : Level} → ℝ⁺ l → nonzero-ℝ l
nonzero-ℝ⁺ (x , is-pos-x) = (x , inr-disjunction is-pos-x)
```

### Negative real numbers are nonzero

```agda
is-nonzero-is-negative-ℝ :
  {l : Level} {x : ℝ l} → is-negative-ℝ x → is-nonzero-ℝ x
is-nonzero-is-negative-ℝ = inl-disjunction

nonzero-ℝ⁻ : {l : Level} → ℝ⁻ l → nonzero-ℝ l
nonzero-ℝ⁻ (x , is-neg-x) = (x , inl-disjunction is-neg-x)
```

### Characterization of equality

```agda
eq-nonzero-ℝ :
  {l : Level} → (x y : nonzero-ℝ l) → (real-nonzero-ℝ x ＝ real-nonzero-ℝ y) →
  x ＝ y
eq-nonzero-ℝ _ _ = eq-type-subtype is-nonzero-prop-ℝ
```
