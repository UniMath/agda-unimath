# Uniformly continuous endomaps on the real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.uniformly-continuous-endomaps-real-numbers where
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
{{#concept "uniformly continuous endomap" Disambiguation="on ℝ" Agda=uniformly-continuous-endomap-ℝ}}
on the [real numbers](real-numbers.dedekind-real-numbers.md) is a function
`f : ℝ → ℝ` such that there [exists](foundation.existential-quantification.md) a
modulus `μ : ℚ⁺ → ℚ⁺`, called a modulus of uniform continuity, such that for all
`x y : ℝ` within a
`μ ε`-[neighborhood](real-numbers.metric-space-of-real-numbers.md) of each
other, `f x` and `f y` are within an `ε`-neighborhood. In other words, it is a
[uniformly continuous map](metric-spaces.uniformly-continuous-maps-metric-spaces.md)
from the [metric space](metric-spaces.metric-spaces.md) of real numbers to
itself.

## Definition

```agda
uniformly-continuous-endomap-ℝ : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
uniformly-continuous-endomap-ℝ l1 l2 =
  uniformly-continuous-map-Metric-Space
    ( metric-space-ℝ l1)
    ( metric-space-ℝ l2)

comp-uniformly-continuous-endomap-ℝ :
  {l1 l2 l3 : Level} →
  uniformly-continuous-endomap-ℝ l2 l3 →
  uniformly-continuous-endomap-ℝ l1 l2 →
  uniformly-continuous-endomap-ℝ l1 l3
comp-uniformly-continuous-endomap-ℝ {l1} {l2} {l3} =
  comp-uniformly-continuous-map-Metric-Space
    ( metric-space-ℝ l1)
    ( metric-space-ℝ l2)
    ( metric-space-ℝ l3)

map-uniformly-continuous-endomap-ℝ :
  {l1 l2 : Level} → uniformly-continuous-endomap-ℝ l1 l2 → ℝ l1 → ℝ l2
map-uniformly-continuous-endomap-ℝ {l1} {l2} =
  map-uniformly-continuous-map-Metric-Space
    ( metric-space-ℝ l1)
    ( metric-space-ℝ l2)
```
