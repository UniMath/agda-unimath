# Absolute convergence of series in the real numbers

```agda
module analysis.absolute-convergence-series-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import analysis.absolute-convergence-series-real-banach-spaces
open import analysis.convergent-series-real-banach-spaces
open import analysis.convergent-series-real-numbers
open import analysis.series-real-banach-spaces
open import analysis.series-real-numbers

open import foundation.function-types
open import foundation.propositions
open import foundation.universe-levels

open import linear-algebra.real-banach-spaces

open import real-numbers.absolute-value-real-numbers
```

</details>

## Idea

A [series](analysis.series-real-numbers.md) `Σ aₙ` of
[real numbers](real-numbers.dedekind-real-numbers.md) is said to
{{#concept "absolutely converge" Agda=is-absolutely-convergent-prop-series-ℝ Disambiguation="series of real numbers"}}
if the series of absolute values `Σ |aₙ|`
[converges](analysis.convergent-series-real-numbers.md).

## Definition

```agda
module _
  {l : Level}
  (σ : series-ℝ l)
  where

  map-abs-series-ℝ : series-ℝ l
  map-abs-series-ℝ = series-terms-ℝ (abs-ℝ ∘ term-series-ℝ σ)

  is-absolutely-convergent-prop-series-ℝ : Prop (lsuc l)
  is-absolutely-convergent-prop-series-ℝ =
    is-convergent-prop-series-ℝ map-abs-series-ℝ

  is-absolutely-convergent-series-ℝ : UU (lsuc l)
  is-absolutely-convergent-series-ℝ =
    type-Prop is-absolutely-convergent-prop-series-ℝ
```

## Properties

### If a series of real numbers is absolutely convergent, it is convergent

```agda
module _
  {l : Level}
  (σ : series-ℝ l)
  where

  is-convergent-is-absolutely-convergent-series-ℝ :
    is-absolutely-convergent-series-ℝ σ →
    is-convergent-series-ℝ σ
  is-convergent-is-absolutely-convergent-series-ℝ H =
    is-convergent-real-is-convergent-real-banach-space-ℝ
      ( term-series-ℝ σ)
      ( is-convergent-is-absolutely-convergent-series-ℝ-Banach-Space
        ( real-banach-space-ℝ l)
        ( series-terms-ℝ-Banach-Space
          ( real-banach-space-ℝ l)
          ( term-series-ℝ σ))
        ( H))
```

## See also

- [Absolute convergence of series in real Banach spaces](analysis.absolute-convergence-series-real-banach-spaces.md)

## External links

- [Absolute convergence](https://en.wikipedia.org/wiki/Absolute_convergence) on
  Wikipedia
