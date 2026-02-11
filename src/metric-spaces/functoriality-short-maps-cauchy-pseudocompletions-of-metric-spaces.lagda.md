# Functorial action on short maps of Cauchy pseudocompletions of metric spaces

```agda
module metric-spaces.functoriality-short-maps-cauchy-pseudocompletions-of-metric-spaces where
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

open import metric-spaces.cauchy-approximations-metric-spaces
open import metric-spaces.cauchy-pseudocompletions-of-metric-spaces
open import metric-spaces.functoriality-short-maps-cauchy-pseudocompletions-of-pseudometric-spaces
open import metric-spaces.limits-of-cauchy-approximations-metric-spaces
open import metric-spaces.metric-spaces
open import metric-spaces.short-maps-metric-spaces
open import metric-spaces.short-maps-pseudometric-spaces
```

</details>

## Idea

The
{{#concept "functorial action" Disambiguation="of Cauchy pseudocompletions on short maps between metric spaces" Agda=short-map-cauchy-pseudocompletion-Metric-Space}}
of
[Cauchy pseudocompletions](metric-spaces.cauchy-pseudocompletions-of-metric-spaces.md)
on [short maps](metric-spaces.short-maps-metric-spaces.md) between
[metric spaces](metric-spaces.metric-spaces.md) is the
[action](metric-spaces.functoriality-short-maps-cauchy-pseudocompletions-of-pseudometric-spaces.md)
on the underlying [pseudometric spaces](metric-spaces.pseudometric-spaces.md).

This action preserves
[limits](metric-spaces.limits-of-cauchy-approximations-metric-spaces.md).

## Definitions

### The action on short maps of Cauchy pseudocompletions

```agda
module _
  {l1 l2 l1' l2' : Level}
  (A : Metric-Space l1 l2) (B : Metric-Space l1' l2')
  (f : short-map-Metric-Space A B)
  where

  short-map-cauchy-pseudocompletion-Metric-Space :
    short-map-Pseudometric-Space
      ( cauchy-pseudocompletion-Metric-Space A)
      ( cauchy-pseudocompletion-Metric-Space B)
  short-map-cauchy-pseudocompletion-Metric-Space =
    short-map-cauchy-pseudocompletion-Pseudometric-Space
      ( pseudometric-Metric-Space A)
      ( pseudometric-Metric-Space B)
      ( f)

  map-short-map-cauchy-pseudocompletion-Metric-Space :
    cauchy-approximation-Metric-Space A →
    cauchy-approximation-Metric-Space B
  map-short-map-cauchy-pseudocompletion-Metric-Space =
    map-short-map-Pseudometric-Space
      ( cauchy-pseudocompletion-Metric-Space A)
      ( cauchy-pseudocompletion-Metric-Space B)
        ( short-map-cauchy-pseudocompletion-Metric-Space)

  preserves-neighborhoods-map-short-map-cauchy-pseudocompletion-Metric-Space :
    is-short-map-Pseudometric-Space
      ( cauchy-pseudocompletion-Metric-Space A)
      ( cauchy-pseudocompletion-Metric-Space B)
      ( map-short-map-cauchy-pseudocompletion-Metric-Space)
  preserves-neighborhoods-map-short-map-cauchy-pseudocompletion-Metric-Space =
    is-short-map-short-map-Pseudometric-Space
      ( cauchy-pseudocompletion-Metric-Space A)
      ( cauchy-pseudocompletion-Metric-Space B)
      ( short-map-cauchy-pseudocompletion-Metric-Space)
```

## Properties

### Functoriality of the action on short maps

```agda
module _
  {l1 l2 : Level}
  (A : Metric-Space l1 l2)
  where abstract

  htpy-id-map-short-map-cauchy-pseudocompletion-Metric-Space :
    map-short-map-cauchy-pseudocompletion-Metric-Space
      ( A)
      ( A)
      ( id-short-map-Metric-Space A) ＝
    id
  htpy-id-map-short-map-cauchy-pseudocompletion-Metric-Space = refl

module _
  {l1a l2a l1b l2b l1c l2c : Level}
  (A : Metric-Space l1a l2a)
  (B : Metric-Space l1b l2b)
  (C : Metric-Space l1c l2c)
  (g : short-map-Metric-Space B C)
  (f : short-map-Metric-Space A B)
  where abstract

  htpy-comp-map-short-map-cauchy-pseudocompletion-Metric-Space :
    ( map-short-map-cauchy-pseudocompletion-Metric-Space B C g ∘
      map-short-map-cauchy-pseudocompletion-Metric-Space A B f) ＝
    ( map-short-map-cauchy-pseudocompletion-Metric-Space A C
      ( comp-short-map-Metric-Space A B C g f))
  htpy-comp-map-short-map-cauchy-pseudocompletion-Metric-Space = refl
```

### The action on short maps on Cauchy pseudocompletions preserves limits

```agda
module _
  {l1 l2 l1' l2' : Level}
  (A : Metric-Space l1 l2) (B : Metric-Space l1' l2')
  (f : short-map-Metric-Space A B)
  (a : cauchy-approximation-Metric-Space A)
  (lim : type-Metric-Space A)
  where abstract

  preserves-limit-map-short-map-cauchy-pseudocompletion-Metric-Space :
    is-limit-cauchy-approximation-Metric-Space A a lim →
    is-limit-cauchy-approximation-Metric-Space
      ( B)
      ( map-short-map-cauchy-pseudocompletion-Metric-Space A B f a)
      ( map-short-map-Metric-Space A B f lim)
  preserves-limit-map-short-map-cauchy-pseudocompletion-Metric-Space
    is-lim-a ε δ =
    is-short-map-short-map-Metric-Space A B
      ( f)
      ( ε +ℚ⁺ δ)
      ( map-cauchy-approximation-Metric-Space A a ε)
      ( lim)
      ( is-lim-a ε δ)
```
