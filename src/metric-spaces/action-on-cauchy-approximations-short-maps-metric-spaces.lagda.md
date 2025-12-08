# The action on Cauchy approximations of short maps between metric spaces

```agda
module metric-spaces.action-on-cauchy-approximations-short-maps-metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-positive-rational-numbers
open import elementary-number-theory.positive-rational-numbers

open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.propositions
open import foundation.subtypes
open import foundation.universe-levels

open import metric-spaces.action-on-cauchy-approximations-short-maps-pseudometric-spaces
open import metric-spaces.cauchy-approximations-metric-spaces
open import metric-spaces.metric-spaces
open import metric-spaces.short-functions-metric-spaces
```

</details>

## Idea

[Short maps](metric-spaces)(metric-spaces.short-functions-metric-spaces.md)
between [metric spaces](metric-spaces.metric-spaces.md) act on
[cauchy approximations](metric-spaces.cauchy-approximations-metric-spaces.md)
and induce a short map between the
[Cauchy pseudocompletions](metric-spaces.cauchy-pseudocompletion-of-metric-spaces.md).

## Definitions

### The action of short maps on Cauchy approximations

```agda
module _
  {l1 l2 l1' l2' : Level}
  (A : Metric-Space l1 l2) (B : Metric-Space l1' l2')
  (f : short-function-Metric-Space A B)
  where

  map-short-function-cauchy-approximation-Metric-Space :
    cauchy-approximation-Metric-Space A →
    cauchy-approximation-Metric-Space B
  map-short-function-cauchy-approximation-Metric-Space =
    map-cauchy-approximation-short-function-Pseudometric-Space
      ( pseudometric-Metric-Space A)
      ( pseudometric-Metric-Space B)
      ( f)
```

## Properties

### Functoriality of the action of short maps

```agda
module _
  {l1 l2 : Level}
  (A : Metric-Space l1 l2)
  where

  htpy-id-map-short-function-cauchy-approximation-Metric-Space :
    map-short-function-cauchy-approximation-Metric-Space
      ( A)
      ( A)
      ( id-short-function-Metric-Space A) ＝
    id
  htpy-id-map-short-function-cauchy-approximation-Metric-Space = refl

module _
  {l1a l2a l1b l2b l1c l2c : Level}
  (A : Metric-Space l1a l2a)
  (B : Metric-Space l1b l2b)
  (C : Metric-Space l1c l2c)
  (g : short-function-Metric-Space B C)
  (f : short-function-Metric-Space A B)
  where

  htpy-comp-map-short-function-cauchy-approximation-Metric-Space :
    ( map-short-function-cauchy-approximation-Metric-Space B C g ∘
      map-short-function-cauchy-approximation-Metric-Space A B f) ＝
    ( map-short-function-cauchy-approximation-Metric-Space A C
      ( comp-short-function-Metric-Space A B C g f))
  htpy-comp-map-short-function-cauchy-approximation-Metric-Space = refl
```
