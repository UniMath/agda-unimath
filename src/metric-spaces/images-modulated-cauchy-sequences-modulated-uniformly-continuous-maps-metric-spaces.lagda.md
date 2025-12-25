# The images of modulated Cauchy sequences under modulated uniformly continuous maps between metric spaces

```agda
module metric-spaces.images-modulated-cauchy-sequences-modulated-uniformly-continuous-maps-metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import lists.sequences

open import metric-spaces.metric-spaces
open import metric-spaces.modulated-cauchy-sequences-metric-spaces
open import metric-spaces.modulated-uniformly-continuous-functions-metric-spaces
open import metric-spaces.sequences-metric-spaces
open import metric-spaces.short-functions-metric-spaces
```

</details>

## Idea

The composition of a
[modulated uniformly continuous map](metric-spaces.modulated-uniformly-continuous-functions-metric-spaces.md)
between [metric spaces](metric-spaces.metric-spaces.md) and a
[modulated Cauchy sequence](metric-spaces.modulated-cauchy-sequences-metric-spaces.md)
is a modulated Cauchy sequence.

## Properties

### Modulated uniformly continuous maps between metric spaces preserve modulated Cauchy sequences

```agda
module _
  {l1 l2 l1' l2' : Level}
  (A : Metric-Space l1 l2) (B : Metric-Space l1' l2')
  (f : modulated-ucont-map-Metric-Space A B)
  (u : modulated-cauchy-sequence-Metric-Space A)
  where

  seq-modulated-ucont-seq-modulated-cauchy-sequence-Metric-Space :
    sequence-type-Metric-Space B
  seq-modulated-ucont-seq-modulated-cauchy-sequence-Metric-Space =
    map-sequence
      ( map-modulated-ucont-map-Metric-Space A B f)
      ( seq-modulated-cauchy-sequence-Metric-Space A u)

  abstract
    cauchy-modulus-modulated-ucont-map-modulated-cauchy-sequence-Metric-Space :
      cauchy-modulus-sequence-Metric-Space B
        ( seq-modulated-ucont-seq-modulated-cauchy-sequence-Metric-Space)
    cauchy-modulus-modulated-ucont-map-modulated-cauchy-sequence-Metric-Space
      ε =
      ( map-modulus-modulated-cauchy-sequence-Metric-Space A u
          (modulus-modulated-ucont-map-Metric-Space A B f ε) ,
        λ m n M≤m M≤n →
          is-modulus-of-uniform-continuity-modulus-modulated-ucont-map-Metric-Space
            ( A)
            ( B)
            ( f)
            ( seq-modulated-cauchy-sequence-Metric-Space A u m)
            ( ε)
            ( seq-modulated-cauchy-sequence-Metric-Space A u n)
            ( neighborhood-map-modulus-modulated-cauchy-sequence-Metric-Space
              ( A)
              ( u)
              ( modulus-modulated-ucont-map-Metric-Space A B f ε)
              ( m)
              ( n)
              ( M≤m)
              ( M≤n)))

  map-modulated-ucont-seq-modulated-cauchy-sequence-Metric-Space :
    modulated-cauchy-sequence-Metric-Space B
  map-modulated-ucont-seq-modulated-cauchy-sequence-Metric-Space =
    ( seq-modulated-ucont-seq-modulated-cauchy-sequence-Metric-Space ,
      cauchy-modulus-modulated-ucont-map-modulated-cauchy-sequence-Metric-Space)
```

### Short maps between metric spaces preserve Cauchy sequences

```agda
module _
  {l1 l2 l1' l2' : Level} (A : Metric-Space l1 l2) (B : Metric-Space l1' l2')
  (f : short-function-Metric-Space A B)
  (u : modulated-cauchy-sequence-Metric-Space A)
  where

  map-short-seq-modulated-cauchy-sequence-Metric-Space :
    modulated-cauchy-sequence-Metric-Space B
  map-short-seq-modulated-cauchy-sequence-Metric-Space =
    map-modulated-ucont-seq-modulated-cauchy-sequence-Metric-Space A B
      ( modulated-ucont-map-short-function-Metric-Space A B f)
      ( u)
```
