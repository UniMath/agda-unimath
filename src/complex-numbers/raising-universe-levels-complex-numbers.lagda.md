# Raising the universe level of complex numbers

```agda
module complex-numbers.raising-universe-levels-complex-numbers where
```

<details><summary>Imports</summary>

```agda
open import complex-numbers.complex-numbers
open import complex-numbers.similarity-complex-numbers

open import foundation.dependent-pair-types
open import foundation.universe-levels

open import real-numbers.raising-universe-levels-real-numbers
```

</details>

## Idea

For every [universe](foundation.universe-levels.md) `𝒰` there is a type of
[complex numbers](complex-numbers.complex-numbers.md) `ℂ` relative to `𝒰`,
`ℂ 𝒰`. Given a larger universe `𝒱`, then we may
{{#concept "raise" Disambiguation="a complex number" Agda=raise-ℂ}} a complex
number `z` from the universe `𝒰` to a
[similar](complex-numbers.similarity-complex-numbers.md) complex number in the
universe `𝒱`.

## Definition

```agda
raise-ℂ : {l1 : Level} (l2 : Level) → ℂ l1 → ℂ (l1 ⊔ l2)
raise-ℂ l (a +iℂ b) = raise-ℝ l a +iℂ raise-ℝ l b
```

## Properties

### Complex numbers are similar to their raised-universe equivalents

```agda
abstract
  sim-raise-ℂ : {l1 : Level} (l2 : Level) (z : ℂ l1) → sim-ℂ z (raise-ℂ l2 z)
  sim-raise-ℂ l (a +iℂ b) = ( sim-raise-ℝ l a , sim-raise-ℝ l b)
```
