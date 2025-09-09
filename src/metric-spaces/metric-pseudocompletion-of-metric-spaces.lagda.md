# The metric pseudocompletion of a metric space

```agda
{-# OPTIONS --lossy-unification #-}

module metric-spaces.metric-pseudocompletion-of-metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import category-theory.isomorphisms-in-precategories

open import elementary-number-theory.positive-rational-numbers
open import elementary-number-theory.strict-inequality-rational-numbers

open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.binary-relations
open import foundation.binary-transport
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.existential-quantification
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.set-quotients
open import foundation.sets
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import metric-spaces.cauchy-approximations-metric-spaces
open import metric-spaces.cauchy-approximations-pseudometric-spaces
open import metric-spaces.complete-metric-spaces
open import metric-spaces.convergent-cauchy-approximations-metric-spaces
open import metric-spaces.equality-of-metric-spaces
open import metric-spaces.functions-metric-spaces
open import metric-spaces.functions-pseudometric-spaces
open import metric-spaces.isometries-metric-spaces
open import metric-spaces.isometries-pseudometric-spaces
open import metric-spaces.limits-of-cauchy-approximations-metric-spaces
open import metric-spaces.limits-of-cauchy-approximations-pseudometric-spaces
open import metric-spaces.metric-pseudocompletion-of-pseudometric-spaces
open import metric-spaces.metric-quotients-of-pseudometric-spaces
open import metric-spaces.metric-spaces
open import metric-spaces.precategory-of-metric-spaces-and-short-functions
open import metric-spaces.pseudometric-completion-of-metric-spaces
open import metric-spaces.pseudometric-completion-of-pseudometric-spaces
open import metric-spaces.pseudometric-spaces
open import metric-spaces.rational-neighborhood-relations
open import metric-spaces.short-functions-metric-spaces
open import metric-spaces.short-functions-pseudometric-spaces
open import metric-spaces.similarity-of-elements-pseudometric-spaces
```

</details>

## Idea

Metric pseudocompletion of metric spaces.

## Definition

### The metric pseudocompletion of a metric space

```agda
module _
  {l1 l2 : Level} (M : Metric-Space l1 l2)
  where

  metric-pseudocompletion-Metric-Space :
    Metric-Space (l1 ⊔ l2) (l1 ⊔ l2)
  metric-pseudocompletion-Metric-Space =
    metric-pseudocompletion-Pseudometric-Space
      ( pseudometric-Metric-Space M)

  pseudometric-metric-pseudocompletion-Metric-Space :
    Pseudometric-Space (l1 ⊔ l2) (l1 ⊔ l2)
  pseudometric-metric-pseudocompletion-Metric-Space =
    pseudometric-Metric-Space
      metric-pseudocompletion-Metric-Space

  type-metric-pseudocompletion-Metric-Space : UU (l1 ⊔ l2)
  type-metric-pseudocompletion-Metric-Space =
    type-Metric-Space metric-pseudocompletion-Metric-Space
```

## Properties

### The isometry from the pseudometric completion of a metric space into its metric pseudocompletion

```agda
module _
  {l1 l2 : Level} (M : Metric-Space l1 l2)
  where

  isometry-metric-pseudocompletion-pseudometric-completion-Metric-Space :
    isometry-Pseudometric-Space
      ( pseudometric-completion-Metric-Space M)
      ( pseudometric-metric-pseudocompletion-Metric-Space M)
  isometry-metric-pseudocompletion-pseudometric-completion-Metric-Space =
    isometry-metric-pseudocompletion-pseudometric-completion-Pseudometric-Space
      ( pseudometric-Metric-Space M)
```

### The isometry from a metric space into its metric pseudocompletion

```agda
module _
  {l1 l2 : Level} (M : Metric-Space l1 l2)
  where

  isometry-metric-pseudocompletion-Metric-Space :
    isometry-Metric-Space
      ( M)
      ( metric-pseudocompletion-Metric-Space M)
  isometry-metric-pseudocompletion-Metric-Space =
    isometry-metric-pseudocompletion-Pseudometric-Space
      ( pseudometric-Metric-Space M)

  map-metric-pseudocompletion-Metric-Space :
    type-function-Metric-Space
      ( M)
      ( metric-pseudocompletion-Metric-Space M)
  map-metric-pseudocompletion-Metric-Space =
    map-isometry-Metric-Space
      ( M)
      ( metric-pseudocompletion-Metric-Space M)
      ( isometry-metric-pseudocompletion-Metric-Space)

  is-isometry-map-metric-pseudocompletion-Metric-Space :
    is-isometry-Metric-Space
      ( M)
      ( metric-pseudocompletion-Metric-Space M)
      ( map-metric-pseudocompletion-Metric-Space)
  is-isometry-map-metric-pseudocompletion-Metric-Space =
    is-isometry-map-isometry-Metric-Space
      ( M)
      ( metric-pseudocompletion-Metric-Space M)
      ( isometry-metric-pseudocompletion-Metric-Space)
```

### A complete metric space is isometrically equivalent to its metric pseudocompletion

```agda
module _
  {l1 l2 : Level} (M : Metric-Space l1 l2)
  (is-complete-M : is-complete-Metric-Space M)
  where

  short-map-lim-metric-pseudocompletion-is-complete-Metric-Space :
    short-function-Metric-Space
      ( metric-pseudocompletion-Metric-Space M)
      ( M)
  short-map-lim-metric-pseudocompletion-is-complete-Metric-Space =
    short-map-short-function-metric-quotient-Pseudometric-Space
      ( pseudometric-completion-Metric-Space M)
      ( M)
      ( short-map-lim-pseudometric-completion-is-complete-Metric-Space
        ( M)
        ( is-complete-M))

  map-lim-metric-pseudocompletion-is-complete-Metric-Space :
    type-function-Metric-Space
      ( metric-pseudocompletion-Metric-Space M)
      ( M)
  map-lim-metric-pseudocompletion-is-complete-Metric-Space =
    map-short-function-Metric-Space
      ( metric-pseudocompletion-Metric-Space M)
      ( M)
      ( short-map-lim-metric-pseudocompletion-is-complete-Metric-Space)

  is-short-map-lim-metric-pseudocompletion-is-completr-Metric-Space :
    is-short-function-Metric-Space
      ( metric-pseudocompletion-Metric-Space M)
      ( M)
      ( map-lim-metric-pseudocompletion-is-complete-Metric-Space)
  is-short-map-lim-metric-pseudocompletion-is-completr-Metric-Space =
    is-short-map-short-function-Metric-Space
      ( metric-pseudocompletion-Metric-Space M)
      ( M)
      ( short-map-lim-metric-pseudocompletion-is-complete-Metric-Space)

  compute-map-lim-metric-pseudocompletion-is-complete-Metric-Space :
    (X : type-metric-pseudocompletion-Metric-Space M) →
    (x : cauchy-approximation-Metric-Space M) →
    is-in-class-metric-quotient-Pseudometric-Space
      ( pseudometric-completion-Metric-Space M)
      ( X)
      ( x) →
    map-lim-metric-pseudocompletion-is-complete-Metric-Space X ＝
    limit-cauchy-approximation-Complete-Metric-Space
      ( M , is-complete-M)
      ( x)
  compute-map-lim-metric-pseudocompletion-is-complete-Metric-Space =
    compute-map-short-function-metric-quotient-Pseudometric-Space
      ( pseudometric-completion-Metric-Space M)
      ( M)
      ( short-map-lim-pseudometric-completion-is-complete-Metric-Space
        ( M)
        (is-complete-M))

  is-section-map-metric-pseudocompletion-is-complete-Metric-Space :
    ( map-metric-pseudocompletion-Metric-Space M ∘
      map-lim-metric-pseudocompletion-is-complete-Metric-Space) ~
    ( id)
  is-section-map-metric-pseudocompletion-is-complete-Metric-Space U =
      let
        open
          do-syntax-trunc-Prop
            ( Id-Prop
              ( set-Metric-Space
                ( metric-pseudocompletion-Metric-Space M))
            ( map-metric-pseudocompletion-Metric-Space M
              ( map-lim-metric-pseudocompletion-is-complete-Metric-Space U))
            ( U))
        in do
          (u , u∈U) ←
            is-inhabited-class-metric-quotient-Pseudometric-Space
              ( pseudometric-completion-Metric-Space M)
              ( U)
          let
            lim-u : type-Metric-Space M
            lim-u =
              limit-cauchy-approximation-Complete-Metric-Space
                ( M , is-complete-M)
                ( u)

            compute-map-lim-U :
              map-lim-metric-pseudocompletion-is-complete-Metric-Space U ＝ lim-u
            compute-map-lim-U =
              compute-map-lim-metric-pseudocompletion-is-complete-Metric-Space
                ( U)
                ( u)
                ( u∈U)

            sim-u-lim-u :
              sim-Pseudometric-Space
                ( pseudometric-completion-Metric-Space M)
                ( u)
                ( const-cauchy-approximation-Metric-Space
                  ( M)
                  ( lim-u))
            sim-u-lim-u =
              sim-const-is-limit-cauchy-approximation-Metric-Space
                ( M)
                ( u)
                ( lim-u)
                ( is-limit-map-lim-pseudometric-completion-is-complete-Metric-Space
                  ( M)
                  ( is-complete-M)
                  ( u))

            [u]=[lim-u] :
              ( map-metric-quotient-Pseudometric-Space
                ( pseudometric-completion-Metric-Space M)
                ( u)) ＝
              ( map-metric-pseudocompletion-Metric-Space M lim-u)
            [u]=[lim-u] =
              apply-effectiveness-quotient-map'
                ( equivalence-relation-sim-Pseudometric-Space
                  ( pseudometric-completion-Metric-Space M))
                ( sim-u-lim-u)
          ( ( ap
              ( map-metric-pseudocompletion-Metric-Space M)
              ( compute-map-lim-U)) ∙
            ( inv [u]=[lim-u]) ∙
            ( eq-set-quotient-equivalence-class-set-quotient
              ( equivalence-relation-sim-Pseudometric-Space
              ( pseudometric-completion-Metric-Space M))
              ( U)
              ( u∈U)))

  is-retraction-map-metric-pseudocompletion-is-complete-Metric-Space :
    ( map-lim-metric-pseudocompletion-is-complete-Metric-Space ∘
      map-metric-pseudocompletion-Metric-Space M) ~
    ( id)
  is-retraction-map-metric-pseudocompletion-is-complete-Metric-Space x =
    ( compute-map-lim-metric-pseudocompletion-is-complete-Metric-Space
      ( map-metric-pseudocompletion-Metric-Space M x)
      ( const-cauchy-approximation-Metric-Space M x)
      ( is-in-class-map-quotient-Pseudometric-Space
        ( pseudometric-completion-Metric-Space M)
        ( const-cauchy-approximation-Metric-Space M x))) ∙
    ( is-retraction-limit-cauchy-approximation-Complete-Metric-Space
      ( M , is-complete-M)
      ( x))

  is-equiv-map-metric-pseudocmpletion-is-complete-Metric-Space :
    is-equiv
      ( map-metric-pseudocompletion-Metric-Space M)
  is-equiv-map-metric-pseudocmpletion-is-complete-Metric-Space =
    is-equiv-is-invertible
      ( map-lim-metric-pseudocompletion-is-complete-Metric-Space)
      ( is-section-map-metric-pseudocompletion-is-complete-Metric-Space)
      ( is-retraction-map-metric-pseudocompletion-is-complete-Metric-Space)
```
