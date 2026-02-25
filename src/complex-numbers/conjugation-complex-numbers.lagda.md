# Conjugation of complex numbers

```agda
module complex-numbers.conjugation-complex-numbers where
```

<details><summary>Imports</summary>

```agda
open import complex-numbers.complex-numbers
open import complex-numbers.raising-universe-levels-complex-numbers

open import foundation.action-on-identifications-functions
open import foundation.identity-types
open import foundation.universe-levels

open import real-numbers.dedekind-real-numbers
open import real-numbers.negation-real-numbers
open import real-numbers.raising-universe-levels-real-numbers
```

</details>

## Idea

The
{{#concept "conjugate" WDID=Q381040 WD="complex conjugate" Disambiguation="of a complex number" Agda=conjugate-ℂ}}
of a [complex number](complex-numbers.complex-numbers.md) `a + bi` is `a - bi`.

## Definition

```agda
conjugate-ℂ : {l : Level} → ℂ l → ℂ l
conjugate-ℂ (a +iℂ b) = a +iℂ neg-ℝ b
```

## Properties

### Conjugation is an involution

```agda
abstract
  is-involution-conjugate-ℂ :
    {l : Level} (z : ℂ l) → conjugate-ℂ (conjugate-ℂ z) ＝ z
  is-involution-conjugate-ℂ (a +iℂ b) = eq-ℂ refl (neg-neg-ℝ b)
```

### Conjugating raised complex numbers

```agda
abstract
  conjugate-raise-ℂ :
    {l0 : Level} (l : Level) (z : ℂ l0) →
    conjugate-ℂ (raise-ℂ l z) ＝ raise-ℂ l (conjugate-ℂ z)
  conjugate-raise-ℂ l (a +iℂ b) = eq-ℂ refl (neg-raise-ℝ l b)
```

### The conjugate of `one-ℂ` is `one-ℂ`

```agda
abstract
  conjugate-one-ℂ : conjugate-ℂ one-ℂ ＝ one-ℂ
  conjugate-one-ℂ = eq-ℂ refl neg-zero-ℝ
```

### The conjugate of `complex-ℝ x` is `complex-ℝ x`

```agda
abstract
  conjugate-complex-ℝ :
    {l : Level} (x : ℝ l) → conjugate-ℂ (complex-ℝ x) ＝ complex-ℝ x
  conjugate-complex-ℝ {l} x =
    eq-ℂ refl (neg-raise-ℝ _ _ ∙ ap (raise-ℝ l) neg-zero-ℝ)
```
