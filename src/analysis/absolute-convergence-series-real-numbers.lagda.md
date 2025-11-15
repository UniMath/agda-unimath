# Absolute convergence of series in the real numbers

```agda
module analysis.absolute-convergence-series-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import analysis.convergent-series-real-banach-spaces
open import analysis.convergent-series-real-numbers
open import analysis.series-real-banach-spaces
open import analysis.series-real-numbers

open import foundation.propositions
open import foundation.universe-levels
```

</details>

## Idea

A [series](analysis.series-real-numbers.md) `Σ aₙ` of
[real numbers](real-numbers.dedekind-real-numbers.md)

is said to
{{#concept "absolutely converge" WDID=Q332465 WD="absolute convergence" Agda=is-absolutely-convergent-prop-series-ℝ Disambiguation="series of real numbers"}}
if the series of absolute values `Σ |aₙ|`
[converges](analysis.convergent-series-real-numbers.md).

## Definition

```agda
module _
  {l : Level}
  (σ : series-ℝ l)
  where

  is-absolutely-convergent-prop-series-ℝ : Prop (lsuc l)
  is-absolutely-convergent-prop-series-ℝ =
    is-convergent-prop-series-ℝ (map-abs-series-ℝ σ)

  is-absolutely-convergent-series-ℝ : UU (lsuc l)
  is-absolutely-convergent-series-ℝ =
    type-Prop is-absolutely-convergent-prop-series-ℝ
```
