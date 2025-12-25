# The images of Cauchy sequences under uniformly continuous maps between metric spaces

```agda
module metric-spaces.images-cauchy-sequences-uniformly-continuous-maps-metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.propositional-truncations
open import foundation.universe-levels

open import lists.sequences

open import metric-spaces.cauchy-sequences-metric-spaces
open import metric-spaces.images-modulated-cauchy-sequences-modulated-uniformly-continuous-maps-metric-spaces
open import metric-spaces.metric-spaces
open import metric-spaces.sequences-metric-spaces
open import metric-spaces.short-functions-metric-spaces
open import metric-spaces.uniformly-continuous-functions-metric-spaces
```

</details>

## Idea

The composition of a
[uniformly continuous map](metric-spaces.uniformly-continuous-functions-metric-spaces.md)
between [metric spaces](metric-spaces.metric-spaces.md) and a
[Cauchy sequence](metric-spaces.cauchy-sequences-metric-spaces.md) is a Cauchy
sequence.

## Properties

### Uniformly continuous maps between metric spaces preserve Cauchy sequences

```agda
module _
  {l1 l2 l1' l2' : Level}
  (A : Metric-Space l1 l2) (B : Metric-Space l1' l2')
  (f : uniformly-continuous-function-Metric-Space A B)
  (x : cauchy-sequence-Metric-Space A)
  where

  seq-uniformly-continuous-map-seq-cauchy-sequence-Metric-Space :
    sequence-type-Metric-Space B
  seq-uniformly-continuous-map-seq-cauchy-sequence-Metric-Space =
    map-sequence
      ( map-uniformly-continuous-function-Metric-Space A B f)
      ( seq-cauchy-sequence-Metric-Space A x)

  abstract
    is-cauchy-sequence-uniformly-continuous-map-cauchy-sequence-Metric-Space :
      is-cauchy-sequence-Metric-Space
        ( B)
        ( seq-uniformly-continuous-map-seq-cauchy-sequence-Metric-Space)
    is-cauchy-sequence-uniformly-continuous-map-cauchy-sequence-Metric-Space =
      let
        open
          do-syntax-trunc-Prop
            ( is-cauchy-sequence-prop-Metric-Space
              ( B)
              ( seq-uniformly-continuous-map-seq-cauchy-sequence-Metric-Space))
      in do
        μf ←
          is-uniformly-continuous-map-uniformly-continuous-function-Metric-Space
            ( A)
            ( B)
            ( f)
        μx ← is-cauchy-sequence-seq-cauchy-sequence-Metric-Space A x
        unit-trunc-Prop
          ( cauchy-modulus-modulated-ucont-map-modulated-cauchy-sequence-Metric-Space
            ( A)
            ( B)
            ( map-uniformly-continuous-function-Metric-Space A B f , μf)
            ( seq-cauchy-sequence-Metric-Space A x , μx))

  map-uniformly-continuous-map-cauchy-sequence-Metric-Space :
    cauchy-sequence-Metric-Space B
  map-uniformly-continuous-map-cauchy-sequence-Metric-Space =
    ( seq-uniformly-continuous-map-seq-cauchy-sequence-Metric-Space ,
      is-cauchy-sequence-uniformly-continuous-map-cauchy-sequence-Metric-Space)
```

### Short maps between metric spaces preserve Cauchy sequences

```agda
module _
  {l1 l2 l1' l2' : Level}
  (A : Metric-Space l1 l2) (B : Metric-Space l1' l2')
  (f : short-function-Metric-Space A B)
  (u : cauchy-sequence-Metric-Space A)
  where

  map-short-map-cauchy-sequence-Metric-Space : cauchy-sequence-Metric-Space B
  map-short-map-cauchy-sequence-Metric-Space =
    map-uniformly-continuous-map-cauchy-sequence-Metric-Space
      ( A)
      ( B)
      ( uniformly-continuous-short-function-Metric-Space A B f)
      ( u)
```
