# The action on Cauchy sequences of uniformly continuous maps between metric spaces

```agda
module metric-spaces.action-on-cauchy-sequences-uniformly-continuous-maps-metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.functoriality-propositional-truncation
open import foundation.propositional-truncations
open import foundation.universe-levels

open import lists.sequences

open import metric-spaces.action-on-modulated-cauchy-sequences-modulated-uniformly-continuous-maps-metric-spaces
open import metric-spaces.cauchy-sequences-metric-spaces
open import metric-spaces.metric-spaces
open import metric-spaces.modulated-cauchy-sequences-metric-spaces
open import metric-spaces.sequences-metric-spaces
open import metric-spaces.uniformly-continuous-maps-metric-spaces
```

</details>

## Idea

The composition of a
[uniformly continuous map](metric-spaces.uniformly-continuous-maps-metric-spaces.md)
between [metric spaces](metric-spaces.metric-spaces.md) and a
[Cauchy sequence](metric-spaces.cauchy-sequences-metric-spaces.md) is a Cauchy
sequence.

## Proof

```agda
module _
  {l1 l2 l1' l2' : Level}
  (A : Metric-Space l1 l2) (B : Metric-Space l1' l2')
  (f : uniformly-continuous-map-Metric-Space A B)
  (x : cauchy-sequence-Metric-Space A)
  where

  sequence-map-cauchy-sequence-uniformly-continuous-map-Metric-Space :
    sequence-type-Metric-Space B
  sequence-map-cauchy-sequence-uniformly-continuous-map-Metric-Space =
    map-sequence
      ( map-uniformly-continuous-map-Metric-Space A B f)
      ( sequence-cauchy-sequence-Metric-Space A x)

  abstract
    is-cauchy-sequence-map-cauchy-sequence-uniformly-continuous-map-Metric-Space :
      is-cauchy-sequence-Metric-Space
        ( B)
        ( sequence-map-cauchy-sequence-uniformly-continuous-map-Metric-Space)
    is-cauchy-sequence-map-cauchy-sequence-uniformly-continuous-map-Metric-Space =
      map-binary-trunc-Prop
        ( λ μf μx →
          cauchy-modulus-map-modulated-cauchy-sequence-modulated-ucont-map-Metric-Space
            ( A)
            ( B)
            ( map-uniformly-continuous-map-Metric-Space A B f , μf)
            ( sequence-cauchy-sequence-Metric-Space A x , μx))
        ( is-uniformly-continuous-map-uniformly-continuous-map-Metric-Space
          ( A)
          ( B)
          ( f))
        ( is-cauchy-sequence-sequence-cauchy-sequence-Metric-Space A x)

  map-cauchy-sequence-uniformly-continuous-map-Metric-Space :
    cauchy-sequence-Metric-Space B
  map-cauchy-sequence-uniformly-continuous-map-Metric-Space =
    ( sequence-map-cauchy-sequence-uniformly-continuous-map-Metric-Space ,
      is-cauchy-sequence-map-cauchy-sequence-uniformly-continuous-map-Metric-Space)
```

## See also

- [The action on Cauchy sequences of short maps between metric spaces](metric-spaces.action-on-cauchy-sequences-short-maps-metric-spaces.md)
