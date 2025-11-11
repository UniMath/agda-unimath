# Uniformly continuous functions of real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.uniformly-continuous-functions-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels

open import metric-spaces.uniformly-continuous-functions-metric-spaces

open import real-numbers.dedekind-real-numbers
open import real-numbers.metric-space-of-real-numbers
```

</details>

## Idea

A
{{#concept "uniformly continuous function" Disambiguation="from ℝ to ℝ" Agda=uniformly-continuous-function-ℝ}}
from the [real numbers](real-numbers.dedekind-real-numbers.md) to the real
numbers is a function `f : ℝ → ℝ` such that there
[exists](foundation.existential-quantification.md) a modulus `μ : ℚ⁺ → ℚ⁺` such
that for all `x y : ℝ` within a
`μ ε`-[neighborhood](real-numbers.metric-space-of-real-numbers.md) of each
other, `f x` and `f y` are within an `ε`-neighborhood.

## Definition

```agda
uniformly-continuous-function-ℝ : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
uniformly-continuous-function-ℝ l1 l2 =
  uniformly-continuous-function-Metric-Space
    ( metric-space-ℝ l1)
    ( metric-space-ℝ l2)

comp-uniformly-continuous-function-ℝ :
  {l1 l2 l3 : Level} →
  uniformly-continuous-function-ℝ l2 l3 →
  uniformly-continuous-function-ℝ l1 l2 →
  uniformly-continuous-function-ℝ l1 l3
comp-uniformly-continuous-function-ℝ {l1} {l2} {l3} =
  comp-uniformly-continuous-function-Metric-Space
    ( metric-space-ℝ l1)
    ( metric-space-ℝ l2)
    ( metric-space-ℝ l3)

map-uniformly-continuous-function-ℝ :
  {l1 l2 : Level} → uniformly-continuous-function-ℝ l1 l2 → ℝ l1 → ℝ l2
map-uniformly-continuous-function-ℝ {l1} {l2} =
  map-uniformly-continuous-function-Metric-Space
    ( metric-space-ℝ l1)
    ( metric-space-ℝ l2)
```
