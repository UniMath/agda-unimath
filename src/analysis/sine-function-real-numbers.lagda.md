# The sine function on the real numbers

```agda
module analysis.sine-function-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import analysis.power-series-at-zero-real-numbers
open import analysis.sine-power-series-real-numbers

open import foundation.universe-levels

open import real-numbers.dedekind-real-numbers
```

</details>

## Idea

The
{{#concept "sine" WDID=Q152415 WD="sine" Disambiguation="of a real number" Agda=sin-ℝ}}
of a [real number](real-numbers.dedekind-real-numbers.md) `x` is the limit of
the [sine power series](analysis.sine-power-series-real-numbers.md) evaluated at
`x`.

## Definition

```agda
sin-ℝ : {l : Level} → ℝ l → ℝ l
sin-ℝ {l} =
  ev-convergent-everywhere-power-series-at-zero-ℝ
    ( sin-convergent-everywhere-power-series-ℝ l)
```

## External links

- [sine](https://en.wikipedia.org/wiki/Sine) on Wikipedia
