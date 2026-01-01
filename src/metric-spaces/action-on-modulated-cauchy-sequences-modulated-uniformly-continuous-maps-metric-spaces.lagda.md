# The images of modulated Cauchy sequences under modulated uniformly continuous maps between metric spaces

```agda
module metric-spaces.action-on-modulated-cauchy-sequences-modulated-uniformly-continuous-maps-metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import lists.sequences

open import metric-spaces.metric-spaces
open import metric-spaces.modulated-cauchy-sequences-metric-spaces
open import metric-spaces.modulated-uniformly-continuous-maps-metric-spaces
open import metric-spaces.sequences-metric-spaces
open import metric-spaces.short-maps-metric-spaces
```

</details>

## Idea

The composition of a
[modulated uniformly continuous map](metric-spaces.modulated-uniformly-continuous-maps-metric-spaces.md)
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

  sequence-map-modulated-cauchy-sequence-modulated-ucont-map-Metric-Space :
    sequence-type-Metric-Space B
  sequence-map-modulated-cauchy-sequence-modulated-ucont-map-Metric-Space =
    map-sequence
      ( map-modulated-ucont-map-Metric-Space A B f)
      ( sequence-modulated-cauchy-sequence-Metric-Space A u)

  abstract
    cauchy-modulus-modulated-cauchy-sequence-modulated-ucont-map-Metric-Space :
      cauchy-modulus-sequence-Metric-Space B
        ( sequence-map-modulated-cauchy-sequence-modulated-ucont-map-Metric-Space)
    cauchy-modulus-modulated-cauchy-sequence-modulated-ucont-map-Metric-Space
      ε =
      let
        (map-f , μf , is-mod-μf) = f
        (seq-u , μu) = u
        (N , H) = μu (μf ε)
      in
        ( N ,
          λ n k N≤n N≤k → is-mod-μf (seq-u n) ε (seq-u k) (H n k N≤n N≤k))

  map-modulated-ucont-sequence-modulated-cauchy-sequence-Metric-Space :
    modulated-cauchy-sequence-Metric-Space B
  map-modulated-ucont-sequence-modulated-cauchy-sequence-Metric-Space =
    ( sequence-map-modulated-cauchy-sequence-modulated-ucont-map-Metric-Space ,
      cauchy-modulus-modulated-cauchy-sequence-modulated-ucont-map-Metric-Space)
```
