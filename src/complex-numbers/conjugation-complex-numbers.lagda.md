# Conjugation of complex numbers

```agda
module complex-numbers.conjugation-complex-numbers where
```

<details><summary>Imports</summary>

```agda
open import complex-numbers.complex-numbers

open import foundation.identity-types
open import foundation.universe-levels

open import real-numbers.negation-real-numbers
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
