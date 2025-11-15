# Nonzero complex numbers

```agda
module complex-numbers.nonzero-complex-numbers where
```

<details><summary>Imports</summary>

```agda
open import complex-numbers.apartness-complex-numbers
open import complex-numbers.complex-numbers
open import complex-numbers.magnitude-complex-numbers

open import foundation.dependent-pair-types
open import foundation.disjunction
open import foundation.propositions
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import real-numbers.addition-nonnegative-real-numbers
open import real-numbers.addition-positive-real-numbers
open import real-numbers.addition-real-numbers
open import real-numbers.nonzero-real-numbers
open import real-numbers.positive-and-negative-real-numbers
open import real-numbers.positive-real-numbers
open import real-numbers.rational-real-numbers
open import real-numbers.similarity-real-numbers
open import real-numbers.square-roots-nonnegative-real-numbers
open import real-numbers.squares-real-numbers
open import real-numbers.strict-inequality-real-numbers
```

</details>

## Idea

A [complex number](complex-numbers.complex-numbers.md) is
{{#concept "nonzero" Agda=is-nonzero-ℂ}} if it is
[apart](complex-numbers.apartness-complex-numbers.md) from zero, that is, its
[real](real-numbers.dedekind-real-numbers.md) part
[or](foundation.disjunction.md) its imaginary part are
[nonzero](real-numbers.nonzero-real-numbers.md).

## Definition

```agda
is-nonzero-prop-ℂ : {l : Level} → ℂ l → Prop l
is-nonzero-prop-ℂ z = apart-prop-ℂ z zero-ℂ

is-nonzero-ℂ : {l : Level} → ℂ l → UU l
is-nonzero-ℂ z = type-Prop (is-nonzero-prop-ℂ z)

nonzero-ℂ : (l : Level) → UU (lsuc l)
nonzero-ℂ l = type-subtype (is-nonzero-prop-ℂ {l})

complex-nonzero-ℂ : {l : Level} → nonzero-ℂ l → ℂ l
complex-nonzero-ℂ = pr1
```

## Properties

### A complex number is nonzero if and only if its squared magnitude is positive

```agda
abstract
  is-positive-squared-magnitude-is-nonzero-ℂ :
    {l : Level} (z : ℂ l) → is-nonzero-ℂ z → is-positive-ℝ ∥ z ∥²ℂ
  is-positive-squared-magnitude-is-nonzero-ℂ (a +iℂ b) =
    elim-disjunction
      ( is-positive-prop-ℝ ∥ a +iℂ b ∥²ℂ)
      ( λ a≠0 →
        concatenate-le-leq-ℝ
          ( zero-ℝ)
          ( square-ℝ a)
          ( square-ℝ a +ℝ square-ℝ b)
          ( is-positive-square-is-nonzero-ℝ a a≠0)
          ( leq-left-add-real-ℝ⁰⁺ _ (nonnegative-square-ℝ b)))
      ( λ b≠0 →
        concatenate-le-leq-ℝ
          ( zero-ℝ)
          ( square-ℝ b)
          ( square-ℝ a +ℝ square-ℝ b)
          ( is-positive-square-is-nonzero-ℝ b b≠0)
          ( leq-right-add-real-ℝ⁰⁺ _ (nonnegative-square-ℝ a)))

  is-nonzero-is-positive-squared-magnitude-ℂ :
    {l : Level} (z : ℂ l) → is-positive-ℝ ∥ z ∥²ℂ → is-nonzero-ℂ z
  is-nonzero-is-positive-squared-magnitude-ℂ (a +iℂ b) 0<a²+b² =
    elim-disjunction
      ( is-nonzero-prop-ℂ (a +iℂ b))
      ( λ 0<a² → inl-disjunction (is-nonzero-square-is-positive-ℝ a 0<a²))
      ( λ 0<b² → inr-disjunction (is-nonzero-square-is-positive-ℝ b 0<b²))
      ( is-positive-either-is-positive-add-ℝ (square-ℝ a) (square-ℝ b) 0<a²+b²)

positive-squared-magnitude-nonzero-ℂ :
  {l : Level} (z : nonzero-ℂ l) → ℝ⁺ l
positive-squared-magnitude-nonzero-ℂ (z , z≠0) =
  ( squared-magnitude-ℂ z , is-positive-squared-magnitude-is-nonzero-ℂ z z≠0)
```

### A complex number is nonzero if and only if its magnitude is positive

```agda
abstract
  is-nonzero-is-positive-magnitude-ℂ :
    {l : Level} (z : ℂ l) → is-positive-ℝ ∥ z ∥ℂ → is-nonzero-ℂ z
  is-nonzero-is-positive-magnitude-ℂ z 0<|z| =
    is-nonzero-is-positive-squared-magnitude-ℂ
      ( z)
      ( is-positive-is-positive-sqrt-ℝ⁰⁺
        ( nonnegative-squared-magnitude-ℂ z)
        ( 0<|z|))

  is-positive-magnitude-is-nonzero-ℂ :
    {l : Level} (z : ℂ l) → is-nonzero-ℂ z → is-positive-ℝ ∥ z ∥ℂ
  is-positive-magnitude-is-nonzero-ℂ z z≠0 =
    is-positive-sqrt-is-positive-ℝ⁰⁺
      ( nonnegative-squared-magnitude-ℂ z)
      ( is-positive-squared-magnitude-is-nonzero-ℂ z z≠0)
```
