# Uniformly continuous endofunctions on the real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.uniformly-continuous-endofunctions-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels

open import metric-spaces.uniformly-continuous-maps-metric-spaces

open import real-numbers.dedekind-real-numbers
open import real-numbers.metric-space-of-real-numbers
```

</details>

## Idea

A
{{#concept "uniformly continuous endofunction" Disambiguation="from ℝ to ℝ" Agda=uniformly-continuous-endo-ℝ}}
on the [real numbers](real-numbers.dedekind-real-numbers.md) is a function
`f : ℝ → ℝ` such that there [exists](foundation.existential-quantification.md) a
modulus `μ : ℚ⁺ → ℚ⁺`, called a modulus of uniform continuity, such that for all
`x y : ℝ` within a
`μ ε`-[neighborhood](real-numbers.metric-space-of-real-numbers.md) of each
other, `f x` and `f y` are within an `ε`-neighborhood.

## Definition

```agda
uniformly-continuous-endo-ℝ : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
uniformly-continuous-endo-ℝ l1 l2 =
  uniformly-continuous-map-Metric-Space
    ( metric-space-ℝ l1)
    ( metric-space-ℝ l2)

comp-uniformly-continuous-endo-ℝ :
  {l1 l2 l3 : Level} →
  uniformly-continuous-endo-ℝ l2 l3 →
  uniformly-continuous-endo-ℝ l1 l2 →
  uniformly-continuous-endo-ℝ l1 l3
comp-uniformly-continuous-endo-ℝ {l1} {l2} {l3} =
  comp-uniformly-continuous-map-Metric-Space
    ( metric-space-ℝ l1)
    ( metric-space-ℝ l2)
    ( metric-space-ℝ l3)

map-uniformly-continuous-endo-ℝ :
  {l1 l2 : Level} → uniformly-continuous-endo-ℝ l1 l2 → ℝ l1 → ℝ l2
map-uniformly-continuous-endo-ℝ {l1} {l2} =
  map-uniformly-continuous-map-Metric-Space
    ( metric-space-ℝ l1)
    ( metric-space-ℝ l2)
```
