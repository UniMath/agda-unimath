# The cosine function on the real numbers

```agda
module analysis.cosine-function-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import analysis.cosine-power-series-real-numbers
open import analysis.power-series-at-zero-real-numbers

open import foundation.universe-levels

open import real-numbers.dedekind-real-numbers
```

</details>

## Idea

The
{{#concept "cosine" WDID=Q1256164 WD="cosine" Disambiguation="of a real number" Agda=cos-ℝ}}
of a [real number](real-numbers.dedekind-real-numbers.md) `x` is the limit of
the [cosine power series](analysis.cosine-power-series-real-numbers.md)
evaluated at `x`.

## Definition

```agda
cos-ℝ : {l : Level} → ℝ l → ℝ l
cos-ℝ {l} =
  ev-convergent-everywhere-power-series-at-zero-ℝ
    ( cos-convergent-everywhere-power-series-ℝ l)
```

## External links

- [Cosine](https://en.wikipedia.org/wiki/Cosine) on Wikipedia
