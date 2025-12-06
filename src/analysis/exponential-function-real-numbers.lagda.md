# The exponential function on the real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module analysis.exponential-function-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import analysis.exponential-power-series-real-numbers
open import analysis.power-series-at-zero-real-numbers

open import foundation.universe-levels

open import real-numbers.dedekind-real-numbers
```

</details>

## Idea

The
{{#concept "natural exponential function" Agda=exp-ℝ WDID=Q47306354 Disambiguation="on ℝ" WD="natural exponential function"}}
on the [real numbers](real-numbers.dedekind-real-numbers.md) is the function
defined by the
[exponential power series](analysis.exponential-power-series-real-numbers.md)
$$∑_{n=0}^{∞} \frac{x^n}{n!}$$

## Definition

```agda
exp-ℝ : {l : Level} → ℝ l → ℝ l
exp-ℝ {l} =
  ev-convergent-everywhere-power-series-at-zero-ℝ
    ( exp-convergent-everywhere-power-series-at-zero-ℝ l)
```

## See also

- [Euler's number e](real-numbers.eulers-number.md)

## External links

- [Exponential function](https://en.wikipedia.org/wiki/Exponential_function) on
  Wikipedia
