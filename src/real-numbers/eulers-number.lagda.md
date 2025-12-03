# Euler's number

```agda
module real-numbers.eulers-number where
```

<details><summary>Imports</summary>

```agda
open import analysis.exponential-power-series-real-numbers
open import analysis.power-series-at-zero-real-numbers

open import foundation.universe-levels

open import real-numbers.dedekind-real-numbers
open import real-numbers.rational-real-numbers
```

</details>

## Idea

Euler's number
{{#concept "e" Disambiguation="Euler's number in ℝ" WDID=Q82435 WD="Euler's number" Agda=e-ℝ}},
approximately 2.71828..., is the result of evaluating the
[exponential power series](analysis.exponential-power-series-real-numbers.md)
at 1.

Note that we define it in terms of the power series instead of the
[exponential function](analysis.exponential-function-real-numbers.md) so that
the page on the exponential function can refer to this one.

## Definition

```agda
e-ℝ : ℝ lzero
e-ℝ =
  ev-convergent-everywhere-power-series-at-zero-ℝ
    ( exp-convergent-everywhere-power-series-at-zero-ℝ lzero)
    ( one-ℝ)
```

## External links

- [e (mathematical constant)](<https://en.wikipedia.org/wiki/E_(mathematical_constant)>)
  on Wikipedia
