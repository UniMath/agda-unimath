# Cauchy pseudocompletions of complete metric space

```agda
module metric-spaces.cauchy-pseudocompletion-of-complete-metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-positive-rational-numbers
open import elementary-number-theory.positive-rational-numbers

open import foundation.action-on-identifications-functions
open import foundation.binary-relations
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import metric-spaces.cauchy-approximations-in-cauchy-pseudocompletions-of-pseudometric-spaces
open import metric-spaces.cauchy-approximations-metric-spaces
open import metric-spaces.cauchy-approximations-pseudometric-spaces
open import metric-spaces.cauchy-pseudocompletion-of-metric-spaces
open import metric-spaces.cauchy-pseudocompletion-of-pseudometric-spaces
open import metric-spaces.complete-metric-spaces
open import metric-spaces.isometries-pseudometric-spaces
open import metric-spaces.limits-of-cauchy-approximations-metric-spaces
open import metric-spaces.limits-of-cauchy-approximations-pseudometric-spaces
open import metric-spaces.maps-pseudometric-spaces
open import metric-spaces.metric-spaces
open import metric-spaces.pseudometric-spaces
open import metric-spaces.rational-neighborhood-relations
open import metric-spaces.short-maps-pseudometric-spaces
open import metric-spaces.similarity-of-elements-pseudometric-spaces
```

</details>

## Idea

Any [complete](metric-spaces.complete-metric-spaces.md) is a
[retract](foundation.retracts-of-types.md) of its
[cauchy pseudocompletion](metric-spaces.cauchy-pseudocompletion-of-metric-spaces.md).

## Properties

### Any complete metric space is a short retract of its Cauchy pseudocompletion

```agda
module _
  {l1 l2 : Level} (M : Metric-Space l1 l2)
  (is-complete-M : is-complete-Metric-Space M)
  where

  map-lim-cauchy-pseudocompletion-is-complete-Metric-Space :
    map-Pseudometric-Space
      ( cauchy-pseudocompletion-Metric-Space M)
      ( pseudometric-Metric-Space M)
  map-lim-cauchy-pseudocompletion-is-complete-Metric-Space =
    limit-cauchy-approximation-Complete-Metric-Space
      ( M , is-complete-M)

  is-limit-map-lim-cauchy-pseudocompletion-is-complete-Metric-Space :
    (u : cauchy-approximation-Metric-Space M) →
    is-limit-cauchy-approximation-Metric-Space
      ( M)
      ( u)
      ( map-lim-cauchy-pseudocompletion-is-complete-Metric-Space u)
  is-limit-map-lim-cauchy-pseudocompletion-is-complete-Metric-Space =
    is-limit-limit-cauchy-approximation-Complete-Metric-Space
      ( M , is-complete-M)

  sim-const-map-lim-cauchy-pseudocompletion-is-complete-Metric-Space :
    (u : cauchy-approximation-Metric-Space M) →
    sim-Pseudometric-Space
      ( cauchy-pseudocompletion-Metric-Space M)
      ( u)
      ( const-cauchy-approximation-Metric-Space
        ( M)
        ( map-lim-cauchy-pseudocompletion-is-complete-Metric-Space u))
  sim-const-map-lim-cauchy-pseudocompletion-is-complete-Metric-Space u =
    sim-const-is-limit-cauchy-approximation-Metric-Space
      ( M)
      ( u)
      ( map-lim-cauchy-pseudocompletion-is-complete-Metric-Space u)
      ( is-limit-map-lim-cauchy-pseudocompletion-is-complete-Metric-Space u)

  is-short-map-const-map-lim-cauchy-pseudocompletion-is-complete-Metric-Space :
    is-short-map-Pseudometric-Space
      ( cauchy-pseudocompletion-Metric-Space M)
      ( cauchy-pseudocompletion-Metric-Space M)
      ( ( const-cauchy-approximation-Metric-Space M) ∘
        ( map-lim-cauchy-pseudocompletion-is-complete-Metric-Space))
  is-short-map-const-map-lim-cauchy-pseudocompletion-is-complete-Metric-Space
    d x y =
      preserves-neighborhoods-sim-Pseudometric-Space
        ( cauchy-pseudocompletion-Metric-Space M)
        { x}
        { const-cauchy-approximation-Metric-Space
          ( M)
          ( map-lim-cauchy-pseudocompletion-is-complete-Metric-Space x)}
        { y}
        { const-cauchy-approximation-Metric-Space
          ( M)
          ( map-lim-cauchy-pseudocompletion-is-complete-Metric-Space y)}
        ( sim-const-map-lim-cauchy-pseudocompletion-is-complete-Metric-Space
          ( x))
        ( sim-const-map-lim-cauchy-pseudocompletion-is-complete-Metric-Space
          ( y))
        ( d)

  is-short-map-lim-cauchy-pseudocompletion-is-complete-Metric-Space :
    is-short-map-Pseudometric-Space
      ( cauchy-pseudocompletion-Metric-Space M)
      ( pseudometric-Metric-Space M)
      ( map-lim-cauchy-pseudocompletion-is-complete-Metric-Space)
  is-short-map-lim-cauchy-pseudocompletion-is-complete-Metric-Space d x y Nxy =
    saturated-neighborhood-Metric-Space
      ( M)
      ( d)
      ( map-lim-cauchy-pseudocompletion-is-complete-Metric-Space x)
      ( map-lim-cauchy-pseudocompletion-is-complete-Metric-Space y)
      ( lemma-saturated-neighborhood-map-lim)
    where

      lemma-saturated-neighborhood-map-lim :
        (δ : ℚ⁺) →
        neighborhood-Metric-Space
          ( M)
          ( d +ℚ⁺ δ)
          ( map-lim-cauchy-pseudocompletion-is-complete-Metric-Space x)
          ( map-lim-cauchy-pseudocompletion-is-complete-Metric-Space y)
      lemma-saturated-neighborhood-map-lim δ =
        tr
          ( is-upper-bound-dist-Metric-Space
            ( M)
            ( map-lim-cauchy-pseudocompletion-is-complete-Metric-Space x)
            ( map-lim-cauchy-pseudocompletion-is-complete-Metric-Space y))
          ( ap (add-ℚ⁺' d) (eq-add-split-ℚ⁺ δ) ∙ commutative-add-ℚ⁺ δ d)
          ( is-short-map-const-map-lim-cauchy-pseudocompletion-is-complete-Metric-Space
            ( d)
            ( x)
            ( y)
            ( Nxy)
            ( left-summand-split-ℚ⁺ δ)
            ( right-summand-split-ℚ⁺ δ))

  short-map-lim-cauchy-pseudocompletion-is-complete-Metric-Space :
    short-map-Pseudometric-Space
      ( cauchy-pseudocompletion-Metric-Space M)
      ( pseudometric-Metric-Space M)
  short-map-lim-cauchy-pseudocompletion-is-complete-Metric-Space =
    ( map-lim-cauchy-pseudocompletion-is-complete-Metric-Space ,
      is-short-map-lim-cauchy-pseudocompletion-is-complete-Metric-Space)

  is-retraction-map-cauchy-pseudocompletion-is-complete-Metric-Space :
    ( map-lim-cauchy-pseudocompletion-is-complete-Metric-Space ∘
      map-unit-cauchy-pseudocompletion-Metric-Space M) ~
    ( id)
  is-retraction-map-cauchy-pseudocompletion-is-complete-Metric-Space =
    is-retraction-limit-cauchy-approximation-Complete-Metric-Space
      ( M , is-complete-M)

  sim-map-lim-cauchy-pseudocompletion-is-complete-Metric-Space :
    (u : cauchy-approximation-Metric-Space M) →
    sim-Pseudometric-Space
      ( cauchy-pseudocompletion-Metric-Space M)
      ( u)
      ( map-unit-cauchy-pseudocompletion-Metric-Space
        ( M)
        ( map-lim-cauchy-pseudocompletion-is-complete-Metric-Space u))
  sim-map-lim-cauchy-pseudocompletion-is-complete-Metric-Space u =
    sim-const-is-limit-cauchy-approximation-Metric-Space
      ( M)
      ( u)
      ( map-lim-cauchy-pseudocompletion-is-complete-Metric-Space u)
      ( is-limit-map-lim-cauchy-pseudocompletion-is-complete-Metric-Space u)
```

### The isometry mapping a Cauchy approximation in a complete metric space to its limit

```agda
module _
  {l1 l2 : Level} (M : Metric-Space l1 l2)
  (is-complete-M : is-complete-Metric-Space M)
  where

  abstract
    reflects-neighborhoods-map-lim-cauchy-pseudocompletion-is-complete-Metric-Space :
      (δ : ℚ⁺) →
      (u v : cauchy-approximation-Metric-Space M) →
      neighborhood-Metric-Space
        ( M)
        ( δ)
        ( map-lim-cauchy-pseudocompletion-is-complete-Metric-Space
          ( M)
          ( is-complete-M)
          ( u))
        ( map-lim-cauchy-pseudocompletion-is-complete-Metric-Space
          ( M)
          ( is-complete-M)
          ( v)) →
      neighborhood-Pseudometric-Space
        ( cauchy-pseudocompletion-Metric-Space M)
        ( δ)
        ( u)
        ( v)
    reflects-neighborhoods-map-lim-cauchy-pseudocompletion-is-complete-Metric-Space
      δ x y Nδ =
      reflects-neighborhoods-sim-Pseudometric-Space
        ( cauchy-pseudocompletion-Metric-Space M)
          { x}
          { const-cauchy-approximation-Metric-Space
            ( M)
            ( map-lim-cauchy-pseudocompletion-is-complete-Metric-Space
              ( M)
              ( is-complete-M)
              ( x))}
          { y}
          { const-cauchy-approximation-Metric-Space
            ( M)
            ( map-lim-cauchy-pseudocompletion-is-complete-Metric-Space
              ( M)
              ( is-complete-M)
              ( y))}
        ( sim-const-map-lim-cauchy-pseudocompletion-is-complete-Metric-Space
          ( M)
          ( is-complete-M)
          ( x))
        ( sim-const-map-lim-cauchy-pseudocompletion-is-complete-Metric-Space
          ( M)
          ( is-complete-M)
          ( y))
        ( δ)
        ( preserves-neighborhoods-map-isometry-Pseudometric-Space
          ( pseudometric-Metric-Space M)
          ( cauchy-pseudocompletion-Metric-Space M)
          ( isometry-unit-cauchy-pseudocompletion-Metric-Space M)
          ( δ)
          ( map-lim-cauchy-pseudocompletion-is-complete-Metric-Space
            ( M)
            ( is-complete-M)
            ( x))
          ( map-lim-cauchy-pseudocompletion-is-complete-Metric-Space
            ( M)
            ( is-complete-M)
            ( y))
          ( Nδ))

    is-isometry-map-lim-cauchy-pseudocompletion-is-complete-Metric-Space :
      is-isometry-Pseudometric-Space
        ( cauchy-pseudocompletion-Metric-Space M)
        ( pseudometric-Metric-Space M)
        ( map-lim-cauchy-pseudocompletion-is-complete-Metric-Space
          ( M)
          ( is-complete-M))
    is-isometry-map-lim-cauchy-pseudocompletion-is-complete-Metric-Space d x y =
      ( ( is-short-map-lim-cauchy-pseudocompletion-is-complete-Metric-Space
          ( M)
          ( is-complete-M)
          ( d)
          ( x)
          ( y)) ,
        ( reflects-neighborhoods-map-lim-cauchy-pseudocompletion-is-complete-Metric-Space
          ( d)
          ( x)
          ( y)))

  isometry-map-lim-cauchy-pseudocompletion-is-complete-Metric-Space :
    isometry-Pseudometric-Space
      ( cauchy-pseudocompletion-Metric-Space M)
      ( pseudometric-Metric-Space M)
  isometry-map-lim-cauchy-pseudocompletion-is-complete-Metric-Space =
    ( ( map-lim-cauchy-pseudocompletion-is-complete-Metric-Space
        ( M)
        ( is-complete-M)) ,
      ( is-isometry-map-lim-cauchy-pseudocompletion-is-complete-Metric-Space))
```
