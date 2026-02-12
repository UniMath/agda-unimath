# Cauchy pseudocompletions of complete metric space

```agda
module metric-spaces.cauchy-pseudocompletions-of-complete-metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-positive-rational-numbers
open import elementary-number-theory.positive-rational-numbers

open import foundation.action-on-identifications-functions
open import foundation.binary-relations
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import metric-spaces.cauchy-approximations-in-cauchy-pseudocompletions-of-pseudometric-spaces
open import metric-spaces.cauchy-approximations-metric-spaces
open import metric-spaces.cauchy-approximations-pseudometric-spaces
open import metric-spaces.cauchy-pseudocompletions-of-metric-spaces
open import metric-spaces.cauchy-pseudocompletions-of-pseudometric-spaces
open import metric-spaces.complete-metric-spaces
open import metric-spaces.isometries-pseudometric-spaces
open import metric-spaces.limits-of-cauchy-approximations-metric-spaces
open import metric-spaces.limits-of-cauchy-approximations-pseudometric-spaces
open import metric-spaces.maps-pseudometric-spaces
open import metric-spaces.metric-spaces
open import metric-spaces.pseudometric-spaces
open import metric-spaces.rational-neighborhood-relations
open import metric-spaces.short-maps-metric-spaces
open import metric-spaces.short-maps-pseudometric-spaces
open import metric-spaces.similarity-of-elements-pseudometric-spaces
open import metric-spaces.universal-property-short-maps-cauchy-pseudocompletions-of-pseudometric-spaces
```

</details>

## Idea

Any [complete](metric-spaces.complete-metric-spaces.md) is a
[retract](foundation.retracts-of-types.md) of its
[cauchy pseudocompletion](metric-spaces.cauchy-pseudocompletions-of-metric-spaces.md).

## Properties

### Any complete metric space is a short retract of its Cauchy pseudocompletion

```agda
module _
  {l1 l2 : Level} (A : Complete-Metric-Space l1 l2)
  where

  retraction-short-map-unit-cauchy-pseudocompletion-Complete-Metric-Space :
    retraction-short-map-Pseudometric-Space
      ( pseudometric-space-Complete-Metric-Space A)
      ( cauchy-pseudocompletion-Metric-Space
        ( metric-space-Complete-Metric-Space A))
      ( short-map-unit-cauchy-pseudocompletion-Metric-Space
        ( metric-space-Complete-Metric-Space A))
  retraction-short-map-unit-cauchy-pseudocompletion-Complete-Metric-Space =
    exten-complete-short-map-cauchy-pseudocompletion-Pseudometric-Space
      ( pseudometric-space-Complete-Metric-Space A)
      ( metric-space-Complete-Metric-Space A)
      ( id-short-map-Metric-Space (metric-space-Complete-Metric-Space A) ,
        is-complete-metric-space-Complete-Metric-Space A)

  short-map-lim-cauchy-pseudocompletion-Complete-Metric-Space :
    short-map-Pseudometric-Space
      ( cauchy-pseudocompletion-Metric-Space
        ( metric-space-Complete-Metric-Space A))
      ( pseudometric-space-Complete-Metric-Space A)
  short-map-lim-cauchy-pseudocompletion-Complete-Metric-Space =
    pr1 retraction-short-map-unit-cauchy-pseudocompletion-Complete-Metric-Space

  map-lim-cauchy-pseudocompletion-Complete-Metric-Space :
    map-Pseudometric-Space
      ( cauchy-pseudocompletion-Metric-Space
        ( metric-space-Complete-Metric-Space A))
      ( pseudometric-space-Complete-Metric-Space A)
  map-lim-cauchy-pseudocompletion-Complete-Metric-Space =
    map-short-map-Pseudometric-Space
      ( cauchy-pseudocompletion-Metric-Space
        ( metric-space-Complete-Metric-Space A))
      ( pseudometric-space-Complete-Metric-Space A)
      ( short-map-lim-cauchy-pseudocompletion-Complete-Metric-Space)

  is-limit-map-lim-cauchy-pseudocompletion-Complete-Metric-Space :
    ( u :
      cauchy-approximation-Metric-Space
        ( metric-space-Complete-Metric-Space A)) →
    is-limit-cauchy-approximation-Metric-Space
      ( metric-space-Complete-Metric-Space A)
      ( u)
      ( map-lim-cauchy-pseudocompletion-Complete-Metric-Space u)
  is-limit-map-lim-cauchy-pseudocompletion-Complete-Metric-Space =
    is-limit-limit-cauchy-approximation-Complete-Metric-Space A

  sim-const-map-lim-cauchy-pseudocompletion-Complete-Metric-Space :
    ( u :
      cauchy-approximation-Metric-Space
        ( metric-space-Complete-Metric-Space A)) →
    sim-Pseudometric-Space
      ( cauchy-pseudocompletion-Metric-Space
        ( metric-space-Complete-Metric-Space A))
      ( u)
      ( const-cauchy-approximation-Metric-Space
        ( metric-space-Complete-Metric-Space A)
        ( map-lim-cauchy-pseudocompletion-Complete-Metric-Space u))
  sim-const-map-lim-cauchy-pseudocompletion-Complete-Metric-Space u =
    sim-const-is-limit-cauchy-approximation-Metric-Space
      ( metric-space-Complete-Metric-Space A)
      ( u)
      ( map-lim-cauchy-pseudocompletion-Complete-Metric-Space u)
      ( is-limit-map-lim-cauchy-pseudocompletion-Complete-Metric-Space u)
```

### The isometry mapping a Cauchy approximation in a complete metric space to its limit

```agda
module _
  {l1 l2 : Level} (M : Complete-Metric-Space l1 l2)
  where abstract

  reflects-neighborhoods-map-lim-cauchy-pseudocompletion-Complete-Metric-Space :
    ( δ : ℚ⁺) →
    ( u v :
      cauchy-approximation-Metric-Space
        ( metric-space-Complete-Metric-Space M)) →
    neighborhood-Metric-Space
      ( metric-space-Complete-Metric-Space M)
      ( δ)
      ( map-lim-cauchy-pseudocompletion-Complete-Metric-Space
        ( M)
        ( u))
      ( map-lim-cauchy-pseudocompletion-Complete-Metric-Space
        ( M)
        ( v)) →
    neighborhood-Pseudometric-Space
      ( cauchy-pseudocompletion-Metric-Space
        ( metric-space-Complete-Metric-Space M))
      ( δ)
      ( u)
      ( v)
  reflects-neighborhoods-map-lim-cauchy-pseudocompletion-Complete-Metric-Space
    δ x y Nδ =
    reflects-neighborhoods-sim-Pseudometric-Space
      ( cauchy-pseudocompletion-Metric-Space
        ( metric-space-Complete-Metric-Space M))
        { x}
        { const-cauchy-approximation-Metric-Space
          ( metric-space-Complete-Metric-Space M)
          ( map-lim-cauchy-pseudocompletion-Complete-Metric-Space
            ( M)
            ( x))}
        { y}
        { const-cauchy-approximation-Metric-Space
          ( metric-space-Complete-Metric-Space M)
          ( map-lim-cauchy-pseudocompletion-Complete-Metric-Space
            ( M)
            ( y))}
      ( sim-const-map-lim-cauchy-pseudocompletion-Complete-Metric-Space
        ( M)
        ( x))
      ( sim-const-map-lim-cauchy-pseudocompletion-Complete-Metric-Space
        ( M)
        ( y))
      ( δ)
      ( preserves-neighborhoods-map-isometry-Pseudometric-Space
        ( pseudometric-space-Complete-Metric-Space M)
        ( cauchy-pseudocompletion-Metric-Space
          ( metric-space-Complete-Metric-Space M))
        ( isometry-unit-cauchy-pseudocompletion-Metric-Space
          ( metric-space-Complete-Metric-Space M))
        ( δ)
        ( map-lim-cauchy-pseudocompletion-Complete-Metric-Space
          ( M)
          ( x))
        ( map-lim-cauchy-pseudocompletion-Complete-Metric-Space
          ( M)
          ( y))
        ( Nδ))

  is-isometry-lim-cauchy-pseudocompletion-Complete-Metric-Space :
    is-isometry-Pseudometric-Space
      ( cauchy-pseudocompletion-Metric-Space
        ( metric-space-Complete-Metric-Space M))
      ( pseudometric-space-Complete-Metric-Space M)
      ( map-lim-cauchy-pseudocompletion-Complete-Metric-Space M)
  is-isometry-lim-cauchy-pseudocompletion-Complete-Metric-Space d x y =
    ( ( is-short-map-short-map-Pseudometric-Space
        ( cauchy-pseudocompletion-Metric-Space
          ( metric-space-Complete-Metric-Space M))
        ( pseudometric-space-Complete-Metric-Space M)
        ( short-map-lim-cauchy-pseudocompletion-Complete-Metric-Space M)
        ( d)
        ( x)
        ( y)) ,
      ( reflects-neighborhoods-map-lim-cauchy-pseudocompletion-Complete-Metric-Space
        ( d)
        ( x)
        ( y)))

module _
  {l1 l2 : Level} (M : Complete-Metric-Space l1 l2)
  where

  isometry-lim-cauchy-pseudocompletion-Complete-Metric-Space :
    isometry-Pseudometric-Space
      ( cauchy-pseudocompletion-Metric-Space
        ( metric-space-Complete-Metric-Space M))
      ( pseudometric-space-Complete-Metric-Space M)
  isometry-lim-cauchy-pseudocompletion-Complete-Metric-Space =
    ( map-lim-cauchy-pseudocompletion-Complete-Metric-Space M ,
      is-isometry-lim-cauchy-pseudocompletion-Complete-Metric-Space M)
```

### The unit map of Cauchy pseudocompletions of complete metric spaces has a unique retraction

```agda
module _
  {l1 l2 : Level}
  (M : Complete-Metric-Space l1 l2)
  where

  is-contr-retraction-short-map-unit-pseudocompletion-Complete-Metric-Space :
    is-contr
      ( retraction-short-map-Pseudometric-Space
        ( pseudometric-space-Complete-Metric-Space M)
        ( cauchy-pseudocompletion-Metric-Space
          ( metric-space-Complete-Metric-Space M))
        ( short-map-unit-cauchy-pseudocompletion-Metric-Space
          ( metric-space-Complete-Metric-Space M)))
  pr1 is-contr-retraction-short-map-unit-pseudocompletion-Complete-Metric-Space
    =
    retraction-short-map-unit-cauchy-pseudocompletion-Complete-Metric-Space M
  pr2 is-contr-retraction-short-map-unit-pseudocompletion-Complete-Metric-Space
    =
    all-eq-extension-short-map-cauchy-pseudocompletion-Pseudometric-Space
      ( pseudometric-space-Complete-Metric-Space M)
      ( metric-space-Complete-Metric-Space M)
      ( id-short-map-Metric-Space
        ( metric-space-Complete-Metric-Space M))
      ( retraction-short-map-unit-cauchy-pseudocompletion-Complete-Metric-Space
        ( M))
```
