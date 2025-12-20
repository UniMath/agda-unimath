# Uniform homeomorphiss between metric spaces

```agda
{-# OPTIONS --lossy-unification #-}

module metric-spaces.uniform-homeomorphisms-metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import foundation.conjunction
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.existential-quantification
open import foundation.function-types
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.retractions
open import foundation.sections
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import metric-spaces.cauchy-sequences-complete-metric-spaces
open import metric-spaces.cauchy-sequences-metric-spaces
open import metric-spaces.complete-metric-spaces
open import metric-spaces.functions-metric-spaces
open import metric-spaces.metric-spaces
open import metric-spaces.uniformly-continuous-functions-metric-spaces
```

</details>

## Idea

A
{{#concept "uniform homeomorphism" WDID=Q2789884 WD="uniform isomorphism" Agda=uniform-homeomorphism-Metric-Space}}
`f` from a [metric space](metric-spaces.metric-spaces.md) `X` to a metric space
`Y` is an [equivalence](foundation.equivalences.md) between `X` and `Y` that is
[uniformly continuous](metric-spaces.uniformly-continuous-functions-metric-spaces.md)
in each direction.

## Definition

```agda
module _
  {l1 l2 l3 l4 : Level}
  (X : Metric-Space l1 l2)
  (Y : Metric-Space l3 l4)
  (f : type-function-Metric-Space X Y)
  where

  is-uniform-homeomorphism-prop-function-Metric-Space : Prop (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  is-uniform-homeomorphism-prop-function-Metric-Space =
    Σ-Prop
      ( is-equiv-Prop f)
      ( λ H →
        ( is-uniformly-continuous-prop-function-Metric-Space X Y f) ∧
        ( is-uniformly-continuous-prop-function-Metric-Space
          ( Y)
          ( X)
          ( map-inv-is-equiv H)))

  is-uniform-homeomorphism-function-Metric-Space : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  is-uniform-homeomorphism-function-Metric-Space =
    type-Prop is-uniform-homeomorphism-prop-function-Metric-Space

uniform-homeomorphism-Metric-Space :
  {l1 l2 l3 l4 : Level} (X : Metric-Space l1 l2) (Y : Metric-Space l3 l4) →
  UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
uniform-homeomorphism-Metric-Space X Y =
  type-subtype (is-uniform-homeomorphism-prop-function-Metric-Space X Y)

module _
  {l1 l2 l3 l4 : Level}
  (X : Metric-Space l1 l2)
  (Y : Metric-Space l3 l4)
  (f : uniform-homeomorphism-Metric-Space X Y)
  where

  map-uniform-homeomorphism-Metric-Space : type-function-Metric-Space X Y
  map-uniform-homeomorphism-Metric-Space = pr1 f

  is-equiv-map-uniform-homeomorphism-Metric-Space :
    is-equiv map-uniform-homeomorphism-Metric-Space
  is-equiv-map-uniform-homeomorphism-Metric-Space = pr1 (pr2 f)

  equiv-uniform-homeomorphism-Metric-Space :
    type-Metric-Space X ≃ type-Metric-Space Y
  equiv-uniform-homeomorphism-Metric-Space =
    ( map-uniform-homeomorphism-Metric-Space ,
      is-equiv-map-uniform-homeomorphism-Metric-Space)

  map-inv-uniform-homeomorphism-Metric-Space : type-function-Metric-Space Y X
  map-inv-uniform-homeomorphism-Metric-Space =
    map-inv-is-equiv is-equiv-map-uniform-homeomorphism-Metric-Space

  is-section-map-inv-uniform-homeomorphism-Metric-Space :
    is-section
      ( map-uniform-homeomorphism-Metric-Space)
      ( map-inv-uniform-homeomorphism-Metric-Space)
  is-section-map-inv-uniform-homeomorphism-Metric-Space =
    is-section-map-inv-equiv
      ( equiv-uniform-homeomorphism-Metric-Space)

  is-retraction-map-inv-uniform-homeomorphism-Metric-Space :
    is-retraction
      ( map-uniform-homeomorphism-Metric-Space)
      ( map-inv-uniform-homeomorphism-Metric-Space)
  is-retraction-map-inv-uniform-homeomorphism-Metric-Space =
    is-retraction-map-inv-equiv
      ( equiv-uniform-homeomorphism-Metric-Space)

  is-uniformly-continuous-map-uniform-homeomorphism-Metric-Space :
    is-uniformly-continuous-function-Metric-Space
      ( X)
      ( Y)
      ( map-uniform-homeomorphism-Metric-Space)
  is-uniformly-continuous-map-uniform-homeomorphism-Metric-Space =
    pr1 (pr2 (pr2 f))

  uniformly-continuous-map-uniform-homeomorphism-Metric-Space :
    uniformly-continuous-function-Metric-Space X Y
  uniformly-continuous-map-uniform-homeomorphism-Metric-Space =
    ( map-uniform-homeomorphism-Metric-Space ,
      is-uniformly-continuous-map-uniform-homeomorphism-Metric-Space)

  is-uniformly-continuous-map-inv-uniform-homeomorphism-Metric-Space :
    is-uniformly-continuous-function-Metric-Space
      ( Y)
      ( X)
      ( map-inv-uniform-homeomorphism-Metric-Space)
  is-uniformly-continuous-map-inv-uniform-homeomorphism-Metric-Space =
    pr2 (pr2 (pr2 f))

  uniformly-continuous-map-inv-uniform-homeomorphism-Metric-Space :
    uniformly-continuous-function-Metric-Space Y X
  uniformly-continuous-map-inv-uniform-homeomorphism-Metric-Space =
    ( map-inv-uniform-homeomorphism-Metric-Space ,
      is-uniformly-continuous-map-inv-uniform-homeomorphism-Metric-Space)

  inv-uniform-homeomorphism-Metric-Space :
    uniform-homeomorphism-Metric-Space Y X
  inv-uniform-homeomorphism-Metric-Space =
    ( map-inv-uniform-homeomorphism-Metric-Space ,
      is-equiv-map-inv-is-equiv
        ( is-equiv-map-uniform-homeomorphism-Metric-Space) ,
      is-uniformly-continuous-map-inv-uniform-homeomorphism-Metric-Space ,
      is-uniformly-continuous-map-uniform-homeomorphism-Metric-Space)
```

## Properties

### Given a uniform homeomorphism between `X` and `Y`, if `X` is complete, so is `Y`

```agda
module _
  {l1 l2 l3 l4 : Level}
  (X : Metric-Space l1 l2)
  (Y : Metric-Space l3 l4)
  (f : uniform-homeomorphism-Metric-Space X Y)
  where

  abstract
    preserves-is-complete-uniform-homeomorphism-Metric-Space :
      is-complete-Metric-Space X →
      is-complete-Metric-Space Y
    preserves-is-complete-uniform-homeomorphism-Metric-Space H =
      let
        open do-syntax-trunc-Prop (is-complete-prop-Metric-Space Y)
      in do
        (μXY , is-mod-μXY) ←
          is-uniformly-continuous-map-uniform-homeomorphism-Metric-Space X Y f
        (μYX , is-mod-μYX) ←
          is-uniformly-continuous-map-inv-uniform-homeomorphism-Metric-Space
            ( X)
            ( Y)
            ( f)
        is-complete-metric-space-cauchy-sequences-have-limits-Metric-Space
          ( Y)
          ( λ uY →
            let
              uX : cauchy-sequence-Metric-Space X
              uX =
                map-modulated-ucont-map-cauchy-sequence-Metric-Space
                  ( Y)
                  ( X)
                  ( map-inv-uniform-homeomorphism-Metric-Space X Y f ,
                    μYX ,
                    is-mod-μYX)
                  ( uY)
              lim-uX = limit-cauchy-sequence-Complete-Metric-Space (X , H) uX
              (μ-uX , is-mod-lim-μ-uX) =
                limit-modulus-limit-cauchy-sequence-Complete-Metric-Space
                  ( X , H)
                  ( uX)
              lim-uY = map-uniform-homeomorphism-Metric-Space X Y f lim-uX
            in
              ( lim-uY ,
                intro-exists
                  ( μ-uX ∘ μXY)
                  ( λ ε n μ-uXμXY≤n →
                    tr
                      ( λ y → neighborhood-Metric-Space Y ε y lim-uY)
                      ( is-section-map-inv-uniform-homeomorphism-Metric-Space
                        ( X)
                        ( Y)
                        ( f)
                        ( map-cauchy-sequence-Metric-Space Y uY n))
                      ( is-mod-μXY
                        ( map-inv-uniform-homeomorphism-Metric-Space
                          ( X)
                          ( Y)
                          ( f)
                          ( map-cauchy-sequence-Metric-Space Y uY n))
                        ( ε)
                        ( lim-uX)
                        ( is-mod-lim-μ-uX
                          ( μXY ε)
                          ( n)
                          ( μ-uXμXY≤n))))))
```
