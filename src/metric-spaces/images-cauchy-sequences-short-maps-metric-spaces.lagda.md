# The images of Cauchy sequences under short maps between metric spaces

```agda
module metric-spaces.images-cauchy-sequences-short-maps-metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels

open import metric-spaces.cauchy-sequences-metric-spaces
open import metric-spaces.images-cauchy-sequences-uniformly-continuous-maps-metric-spaces
open import metric-spaces.metric-spaces
open import metric-spaces.short-maps-metric-spaces
open import metric-spaces.uniformly-continuous-maps-metric-spaces
```

</details>

## Idea

The composition of a [short map](metric-spaces.short-maps-metric-spaces.md)
between [metric spaces](metric-spaces.metric-spaces.md) and a
[Cauchy sequence](metric-spaces.cauchy-sequences-metric-spaces.md) is a Cauchy
sequence.

## Proof

```agda
module _
  {l1 l2 l1' l2' : Level}
  (A : Metric-Space l1 l2) (B : Metric-Space l1' l2')
  (f : short-map-Metric-Space A B)
  (u : cauchy-sequence-Metric-Space A)
  where

  map-cauchy-sequence-short-map-Metric-Space :
    cauchy-sequence-Metric-Space B
  map-cauchy-sequence-short-map-Metric-Space =
    map-cauchy-sequence-uniformly-continuous-map-Metric-Space
      ( A)
      ( B)
      ( uniformly-continuous-map-short-map-Metric-Space A B f)
      ( u)
```

## See also

- [The images of Cauchy sequences under uniformly continuous maps in metric spaces](metric-spaces.images-cauchy-sequences-uniformly-continuous-maps-metric-spaces.md)
