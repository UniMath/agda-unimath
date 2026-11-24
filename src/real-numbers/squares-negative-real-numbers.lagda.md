# Squares of negative real numbers

```agda
module real-numbers.squares-negative-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import real-numbers.multiplication-negative-real-numbers
open import real-numbers.negative-real-numbers
open import real-numbers.positive-real-numbers
open import real-numbers.squares-real-numbers
```

</details>

## Idea

The
{{#concept "square" Disambiguation="of a negative real number" Agda=square-ℝ⁻}}
of a [negative real number](real-numbers.negative-real-numbers.md) `x` is the
[positive real number](real-numbers.positive-real-numbers.md) obtained by
[multiplying](real-numbers.multiplication-negative-real-numbers.md) `x` by
itself.

## Definition

```agda
square-ℝ⁻ : {l : Level} → ℝ⁻ l → ℝ⁺ l
square-ℝ⁻ x = x *ℝ⁻ x

is-positive-square-real-ℝ⁻ :
  {l : Level} (x : ℝ⁻ l) → is-positive-ℝ (square-ℝ (real-ℝ⁻ x))
is-positive-square-real-ℝ⁻ x = is-positive-real-ℝ⁺ (square-ℝ⁻ x)
```
