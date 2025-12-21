# Real complex numbers

```agda
module complex-numbers.real-complex-numbers where
```

<details><summary>Imports</summary>

```agda
open import complex-numbers.complex-numbers
open import complex-numbers.conjugation-complex-numbers

open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.fibers-of-maps
open import foundation.identity-types
open import foundation.images
open import foundation.propositional-truncations
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import real-numbers.dedekind-real-numbers
open import real-numbers.negation-real-numbers
open import real-numbers.rational-real-numbers
open import real-numbers.zero-real-numbers
```

</details>

## Idea

A [complex number](complex-numbers.complex-numbers.md) is
{{#concept "real" Disambiguation="predicate on ℂ" Agda=is-real-prop-ℂ}} if its
imaginary part is zero.

## Definition

```agda
is-real-prop-ℂ : {l : Level} → subtype l (ℂ l)
is-real-prop-ℂ (a +iℂ b) = is-zero-prop-ℝ b

is-real-ℂ : {l : Level} → ℂ l → UU l
is-real-ℂ = is-in-subtype is-real-prop-ℂ
```

## Properties

### `z` is a real complex number if and only if it equals its conjugate

```agda
abstract
  is-real-eq-conjugate-ℂ :
    {l : Level} (z : ℂ l) → conjugate-ℂ z ＝ z → is-real-ℂ z
  is-real-eq-conjugate-ℂ _ a-bi=a+bi = is-zero-eq-neg-ℝ (ap im-ℂ a-bi=a+bi)

  eq-conjugate-is-real-ℂ :
    {l : Level} (z : ℂ l) → is-real-ℂ z → conjugate-ℂ z ＝ z
  eq-conjugate-is-real-ℂ (a +iℂ b) b=0 = eq-ℂ refl (eq-neg-is-zero-ℝ b=0)
```

### `x` is a real complex number if and only if it is in the image of `complex-ℝ`

```agda
abstract
  eq-complex-re-is-real-ℂ :
    {l : Level} (z : ℂ l) → is-real-ℂ z → complex-ℝ (re-ℂ z) ＝ z
  eq-complex-re-is-real-ℂ (a +iℂ b) b=0 =
    eq-ℂ refl (inv (eq-raise-zero-is-zero-ℝ b=0))

  fiber-complex-is-real-ℂ :
    {l : Level} (z : ℂ l) → is-real-ℂ z → fiber complex-ℝ z
  fiber-complex-is-real-ℂ z imz=0 = (re-ℂ z , eq-complex-re-is-real-ℂ z imz=0)

  is-in-im-complex-is-real-ℂ :
    {l : Level} (z : ℂ l) → is-real-ℂ z → is-in-im complex-ℝ z
  is-in-im-complex-is-real-ℂ z imz=0 =
    unit-trunc-Prop (fiber-complex-is-real-ℂ z imz=0)

  is-real-complex-ℝ :
    {l : Level} (a : ℝ l) → is-real-ℂ (complex-ℝ a)
  is-real-complex-ℝ {l} _ = is-zero-raise-zero-ℝ l

  is-real-is-in-im-complex-ℂ :
    {l : Level} (z : ℂ l) → is-in-im complex-ℝ z → is-real-ℂ z
  is-real-is-in-im-complex-ℂ {l} z =
    rec-trunc-Prop
      ( is-real-prop-ℂ z)
      ( λ (a , a=z) → tr is-real-ℂ a=z (is-real-complex-ℝ a))
```
