# Uniformly continuous maps from inhabited, totally bounded metric spaces to normed real vector spaces

```agda
module functional-analysis.metric-space-of-uniformly-continuous-maps-inhabited-totally-bounded-metric-spaces-normed-real-vector-spaces where
```

<details><summary>Imports</summary>

```agda
open import foundation.sets
open import foundation.universe-levels

open import linear-algebra.normed-real-vector-spaces

open import metric-spaces.inhabited-totally-bounded-metric-spaces
open import metric-spaces.metric-space-of-uniformly-continuous-maps-metric-spaces
open import metric-spaces.metric-spaces
open import metric-spaces.uniformly-continuous-maps-metric-spaces
```

</details>

## Idea

The
[uniformly continuous maps](metric-spaces.uniformly-continuous-maps-metric-spaces.md)
from an
[inhabited totally bounded metric space](metric-spaces.inhabited-totally-bounded-metric-spaces.md)
to a [normed real vector space](linear-algebra.normed-real-vector-spaces.md)
themselves form a [metric space](metric-spaces.metric-spaces.md).

## Definition

```agda
module _
  {l1 l2 l3 l4 l5 : Level}
  (X : inhabited-totally-bounded-Metric-Space l1 l2 l3)
  (V : Normed-ℝ-Vector-Space l4 l5)
  where

  metric-space-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Vector-Space :
    Metric-Space (l1 ⊔ l2 ⊔ l4 ⊔ l5) (l1 ⊔ l4)
  metric-space-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Vector-Space =
    metric-space-of-uniformly-continuous-maps-Metric-Space
      ( metric-space-inhabited-totally-bounded-Metric-Space X)
      ( metric-space-Normed-ℝ-Vector-Space V)

  set-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Vector-Space :
    Set (l1 ⊔ l2 ⊔ l4 ⊔ l5)
  set-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Vector-Space =
    set-Metric-Space
      ( metric-space-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Vector-Space)

  uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Vector-Space :
    UU (l1 ⊔ l2 ⊔ l4 ⊔ l5)
  uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Vector-Space =
    type-Set
      ( set-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Vector-Space)
```
