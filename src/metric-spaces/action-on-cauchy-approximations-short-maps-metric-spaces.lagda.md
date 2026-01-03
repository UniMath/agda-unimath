# The action on Cauchy approximations of short maps between metric spaces

```agda
module metric-spaces.action-on-cauchy-approximations-short-maps-metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-positive-rational-numbers
open import elementary-number-theory.positive-rational-numbers

open import foundation.function-types
open import foundation.identity-types
open import foundation.universe-levels

open import metric-spaces.action-on-cauchy-approximations-short-maps-pseudometric-spaces
open import metric-spaces.cauchy-approximations-metric-spaces
open import metric-spaces.cauchy-pseudocompletion-of-metric-spaces
open import metric-spaces.limits-of-cauchy-approximations-metric-spaces
open import metric-spaces.metric-spaces
open import metric-spaces.short-maps-metric-spaces
open import metric-spaces.short-maps-pseudometric-spaces
```

</details>

## Idea

[Short maps](metric-spaces.short-maps-metric-spaces.md) between
[metric spaces](metric-spaces.metric-spaces.md) act on
[cauchy approximations](metric-spaces.cauchy-approximations-metric-spaces.md)
and induce a short map between the
[Cauchy pseudocompletions](metric-spaces.cauchy-pseudocompletion-of-metric-spaces.md).

This action is functorial and preserves
[limits](metric-spaces.limits-of-cauchy-approximations-metric-spaces.md).

## Definitions

### The action of short maps on Cauchy approximations

```agda
module _
  {l1 l2 l1' l2' : Level}
  (A : Metric-Space l1 l2) (B : Metric-Space l1' l2')
  (f : short-map-Metric-Space A B)
  where

  short-map-cauchy-pseudocompletion-short-map-Metric-Space :
    short-map-Pseudometric-Space
      ( cauchy-pseudocompletion-Metric-Space A)
      ( cauchy-pseudocompletion-Metric-Space B)
  short-map-cauchy-pseudocompletion-short-map-Metric-Space =
    short-map-cauchy-approximation-short-map-Pseudometric-Space
      ( pseudometric-Metric-Space A)
      ( pseudometric-Metric-Space B)
      ( f)

  map-cauchy-approximation-short-map-Metric-Space :
    cauchy-approximation-Metric-Space A →
    cauchy-approximation-Metric-Space B
  map-cauchy-approximation-short-map-Metric-Space =
    map-short-map-Pseudometric-Space
      ( cauchy-pseudocompletion-Metric-Space A)
      ( cauchy-pseudocompletion-Metric-Space B)
        ( short-map-cauchy-pseudocompletion-short-map-Metric-Space)

  preserves-neighborhoods-map-cauchy-approximation-short-map-Metric-Space :
    is-short-map-Pseudometric-Space
      ( cauchy-pseudocompletion-Metric-Space A)
      ( cauchy-pseudocompletion-Metric-Space B)
      ( map-cauchy-approximation-short-map-Metric-Space)
  preserves-neighborhoods-map-cauchy-approximation-short-map-Metric-Space =
    is-short-map-short-map-Pseudometric-Space
      ( cauchy-pseudocompletion-Metric-Space A)
      ( cauchy-pseudocompletion-Metric-Space B)
      ( short-map-cauchy-pseudocompletion-short-map-Metric-Space)
```

## Properties

### Functoriality of the action of short maps

```agda
module _
  {l1 l2 : Level}
  (A : Metric-Space l1 l2)
  where abstract

  htpy-id-map-cauchy-approximation-short-map-Metric-Space :
    map-cauchy-approximation-short-map-Metric-Space
      ( A)
      ( A)
      ( id-short-map-Metric-Space A) ＝
    id
  htpy-id-map-cauchy-approximation-short-map-Metric-Space = refl

module _
  {l1a l2a l1b l2b l1c l2c : Level}
  (A : Metric-Space l1a l2a)
  (B : Metric-Space l1b l2b)
  (C : Metric-Space l1c l2c)
  (g : short-map-Metric-Space B C)
  (f : short-map-Metric-Space A B)
  where abstract

  htpy-comp-map-cauchy-approximation-short-map-Metric-Space :
    ( map-cauchy-approximation-short-map-Metric-Space B C g ∘
      map-cauchy-approximation-short-map-Metric-Space A B f) ＝
    ( map-cauchy-approximation-short-map-Metric-Space A C
      ( comp-short-map-Metric-Space A B C g f))
  htpy-comp-map-cauchy-approximation-short-map-Metric-Space = refl
```

### The action of short maps on Cauchy approximations preserves limits

```agda
module _
  {l1 l2 l1' l2' : Level}
  (A : Metric-Space l1 l2) (B : Metric-Space l1' l2')
  (f : short-map-Metric-Space A B)
  (a : cauchy-approximation-Metric-Space A)
  (lim : type-Metric-Space A)
  where abstract

  preserves-limit-map-cauchy-approximation-short-map-Metric-Space :
    is-limit-cauchy-approximation-Metric-Space A a lim →
    is-limit-cauchy-approximation-Metric-Space
      ( B)
      ( map-cauchy-approximation-short-map-Metric-Space A B f a)
      ( map-short-map-Metric-Space A B f lim)
  preserves-limit-map-cauchy-approximation-short-map-Metric-Space
    is-lim-a ε δ =
    is-short-map-short-map-Metric-Space A B
      ( f)
      ( ε +ℚ⁺ δ)
      ( map-cauchy-approximation-Metric-Space A a ε)
      ( lim)
      ( is-lim-a ε δ)
```
