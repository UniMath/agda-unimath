# The real vector space of uniformly continuous maps from inhabited, totally bounded metric spaces to normed real vector spaces

```agda
module functional-analysis.real-vector-space-of-uniformly-continuous-maps-inhabited-totally-bounded-metric-spaces-normed-real-vector-spaces where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels

open import functional-analysis.metric-space-of-uniformly-continuous-maps-inhabited-totally-bounded-metric-spaces-normed-real-vector-spaces

open import linear-algebra.normed-real-vector-spaces
open import linear-algebra.real-vector-spaces
open import linear-algebra.real-vector-spaces-uniformly-continuous-maps-normed-real-vector-spaces

open import metric-spaces.inhabited-totally-bounded-metric-spaces

open import real-numbers.dedekind-real-numbers
```

</details>

## Idea

The
[uniformly continuous maps](metric-spaces.uniformly-continuous-maps-metric-spaces.md)
from
[inhabited, totally bounded metric spaces](metric-spaces.inhabited-totally-bounded-metric-spaces.md)
to [normed real vector spaces](linear-algebra.normed-real-vector-spaces.md) form
a [real vector space](linear-algebra.real-vector-spaces.md).

## Definition

```agda
module _
  {l1 l2 l3 l4 l5 : Level}
  (X : inhabited-totally-bounded-Metric-Space l1 l2 l3)
  (V : Normed-ℝ-Vector-Space l4 l5)
  where

  vector-space-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Vector-Space :
    ℝ-Vector-Space l4 (l1 ⊔ l2 ⊔ l4 ⊔ l5)
  vector-space-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Vector-Space =
    vector-space-uniformly-continuous-map-metric-space-Normed-ℝ-Vector-Space
      ( metric-space-inhabited-totally-bounded-Metric-Space X)
      ( V)

  scalar-mul-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Vector-Space :
    ℝ l4 →
    uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Vector-Space
      ( X)
      ( V) →
    uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Vector-Space
      ( X)
      ( V)
  scalar-mul-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Vector-Space =
    mul-ℝ-Vector-Space
      ( vector-space-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Vector-Space)
```

## See also

- [The supremum norm on this vector space](functional-analysis.supremum-norm-maps-inhabited-totally-bounded-metric-spaces-normed-real-vector-spaces.md)
