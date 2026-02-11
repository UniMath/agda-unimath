# Functorial action on isometries of Cauchy pseudocompletions of metric spaces

```agda
module metric-spaces.functoriality-isometries-cauchy-pseudocompletions-of-metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-positive-rational-numbers
open import elementary-number-theory.positive-rational-numbers

open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.homotopies
open import foundation.universe-levels

open import metric-spaces.cauchy-approximations-metric-spaces
open import metric-spaces.cauchy-approximations-pseudometric-spaces
open import metric-spaces.cauchy-pseudocompletions-of-metric-spaces
open import metric-spaces.cauchy-pseudocompletions-of-pseudometric-spaces
open import metric-spaces.functoriality-isometries-cauchy-pseudocompletions-of-pseudometric-spaces
open import metric-spaces.isometries-metric-spaces
open import metric-spaces.isometries-pseudometric-spaces
open import metric-spaces.maps-pseudometric-spaces
open import metric-spaces.metric-spaces
open import metric-spaces.pseudometric-spaces
open import metric-spaces.short-maps-pseudometric-spaces
```

</details>

## Idea

[Isometries](metric-spaces.isometries-metric-spaces.md) between
[metric spaces](metric-spaces.metric-spaces.md) act on
[Cauchy approximations](metric-spaces.cauchy-approximations-metric-spaces.md)
and induce an [isometry](metric-spaces.isometries-pseudometric-spaces.md)
between the
[Cauchy pseudocompletions](metric-spaces.cauchy-pseudocompletions-of-metric-spaces.md).

## Definitions

### The isometric action on isometries of Cauchy pseudocompletions

```agda
module _
  {l1 l2 l1' l2' : Level}
  (A : Metric-Space l1 l2) (B : Metric-Space l1' l2')
  (f : isometry-Metric-Space A B)
  where

  isometry-cauchy-pseudocompletion-Metric-Space :
    isometry-Pseudometric-Space
      ( cauchy-pseudocompletion-Metric-Space A)
      ( cauchy-pseudocompletion-Metric-Space B)
  isometry-cauchy-pseudocompletion-Metric-Space =
    isometry-cauchy-pseudocompletion-Pseudometric-Space
      ( pseudometric-Metric-Space A)
      ( pseudometric-Metric-Space B)
      ( f)

  map-isometry-cauchy-pseudocompletion-Metric-Space :
    map-Pseudometric-Space
      ( cauchy-pseudocompletion-Metric-Space A)
      ( cauchy-pseudocompletion-Metric-Space B)
  map-isometry-cauchy-pseudocompletion-Metric-Space =
    map-isometry-cauchy-pseudocompletion-Pseudometric-Space
      ( pseudometric-Metric-Space A)
      ( pseudometric-Metric-Space B)
      ( f)
```

## Properties

### The action of isometries preserves homotopies

```agda
module _
  {l1 l2 l1' l2' : Level}
  (A : Metric-Space l1 l2) (B : Metric-Space l1' l2')
  (f g : isometry-Metric-Space A B)
  (f~g : htpy-map-isometry-Metric-Space A B f g)
  where abstract

  htpy-map-isometry-cauchy-pseudocompletion-Metric-Space :
    map-isometry-cauchy-pseudocompletion-Metric-Space A B f ~
    map-isometry-cauchy-pseudocompletion-Metric-Space A B g
  htpy-map-isometry-cauchy-pseudocompletion-Metric-Space u =
    eq-htpy-cauchy-approximation-Metric-Space B
      ( f~g ∘ map-cauchy-approximation-Metric-Space A u)
```

### The action of isometries preserves composition

```agda
module _
  {la la' lb lb' lc lc' : Level}
  (A : Metric-Space la la')
  (B : Metric-Space lb lb')
  (C : Metric-Space lc lc')
  (g : isometry-Metric-Space B C)
  (f : isometry-Metric-Space A B)
  where

  htpy-comp-map-isometry-cauchy-pseudocompletion-Metric-Space :
    ( map-isometry-cauchy-pseudocompletion-Metric-Space B C g ∘
      map-isometry-cauchy-pseudocompletion-Metric-Space A B f) ~
    ( map-isometry-cauchy-pseudocompletion-Metric-Space A C
      ( comp-isometry-Metric-Space A B C g f))
  htpy-comp-map-isometry-cauchy-pseudocompletion-Metric-Space u =
    eq-htpy-cauchy-approximation-Metric-Space C refl-htpy
```
