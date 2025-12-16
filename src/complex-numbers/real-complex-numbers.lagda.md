# Real complex numbers

```agda
module complex-numbers.real-complex-numbers where
```

<details><summary>Imports</summary>

```agda
open import complex-numbers.complex-numbers
open import complex-numbers.conjugation-complex-numbers

open import foundation.sets
open import foundation.subtypes
open import foundation.universe-levels

open import real-numbers.dedekind-real-numbers
open import real-numbers.rational-real-numbers
```

</details>

## Idea

A [complex number](complex-numbers.complex-numbers.md) is
{{#concept "real" Disambiguation="predicate on ℂ" Agda=is-real-prop-ℂ}} if its
imaginary part is zero.

## Definition

```agda
is-real-prop-ℂ : {l : Level} → subtype (lsuc l) (ℂ l)
is-real-prop-ℂ {l} (a +iℂ b) =
  Id-Prop (ℝ-Set l) {!   !} {!   !}
```
