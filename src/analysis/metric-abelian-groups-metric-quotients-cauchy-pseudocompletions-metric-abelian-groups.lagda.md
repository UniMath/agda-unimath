# The metric abelian group of the metric quotient of the Cauchy pseudocompletion of metric abelian groups

```agda
{-# OPTIONS --lossy-unification #-}

module analysis.metric-abelian-groups-metric-quotients-cauchy-pseudocompletions-metric-abelian-groups where
```

<details><summary>Imports</summary>

```agda
open import analysis.abelian-groups-metric-quotients-cauchy-pseudocompletions-metric-abelian-groups
open import analysis.addition-cauchy-approximations-metric-abelian-groups
open import analysis.cauchy-pseudocompletions-metric-abelian-groups
open import analysis.metric-abelian-groups
open import analysis.metric-quotients-cauchy-pseudocompletions-metric-abelian-groups

open import elementary-number-theory.positive-rational-numbers

open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.binary-transport
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.propositional-truncations
open import foundation.set-quotients
open import foundation.universe-levels

open import group-theory.abelian-groups
open import group-theory.homomorphisms-abelian-groups

open import metric-spaces.cauchy-pseudocompletions-of-metric-spaces
open import metric-spaces.functoriality-isometries-cauchy-pseudocompletions-of-metric-spaces
open import metric-spaces.isometries-metric-spaces
open import metric-spaces.isometries-pseudometric-spaces
open import metric-spaces.metric-spaces
open import metric-spaces.short-maps-metric-spaces
open import metric-spaces.short-maps-pseudometric-spaces
open import metric-spaces.unit-map-metric-quotients-of-pseudometric-spaces
```

</details>

## Idea

The [metric quotient](metric-spaces.metric-quotients-of-pseudometric-spaces.md)
of the
[Cauchy pseudocompletion](analysis.cauchy-pseudocompletions-metric-abelian-groups.md)
of a [metric abelian group](analysis.metric-abelian-groups.md) is itself a
metric abelian group.

## Proof

### Negation is a short map

```agda
module _
  {l1 l2 : Level}
  (G : Metric-Ab l1 l2)
  where abstract

  is-short-map-neg-metric-quotient-cauchy-pseudocompletion-Metric-Ab :
    is-short-map-Metric-Space
      ( metric-quotient-cauchy-pseudocompletion-Metric-Ab G)
      ( metric-quotient-cauchy-pseudocompletion-Metric-Ab G)
      ( neg-metric-quotient-cauchy-pseudocompletion-Metric-Ab G)
  is-short-map-neg-metric-quotient-cauchy-pseudocompletion-Metric-Ab
    d x y Ndxy =
    let
      open
        do-syntax-trunc-Prop
          ( neighborhood-prop-metric-quotient-cauchy-pseudocompletion-Metric-Ab
            ( G)
            ( d)
            ( neg-metric-quotient-cauchy-pseudocompletion-Metric-Ab G x)
            ( neg-metric-quotient-cauchy-pseudocompletion-Metric-Ab G y))
    in do
      (x' , ux'=x) ←
        is-surjective-quotient-map
          ( equivalence-relation-sim-cauchy-pseudocompletion-Metric-Ab G)
          ( x)
      (y' , uy'=y) ←
        is-surjective-quotient-map
          ( equivalence-relation-sim-cauchy-pseudocompletion-Metric-Ab G)
          ( y)
      binary-tr
        ( neighborhood-metric-quotient-cauchy-pseudocompletion-Metric-Ab G d)
        ( ( inv
            ( neg-in-approximation-metric-quotient-cauchy-pseudocompletion-Metric-Ab
              ( G)
              ( x'))) ∙
          ( ap (neg-metric-quotient-cauchy-pseudocompletion-Metric-Ab G) ux'=x))
        ( ( inv
            ( neg-in-approximation-metric-quotient-cauchy-pseudocompletion-Metric-Ab
              ( G)
              ( y'))) ∙
          ( ap (neg-metric-quotient-cauchy-pseudocompletion-Metric-Ab G) uy'=y))
        ( preserves-neighborhoods-map-isometry-Pseudometric-Space
          ( cauchy-pseudocompletion-Metric-Ab G)
          ( pseudometric-Metric-Space
            ( metric-quotient-cauchy-pseudocompletion-Metric-Ab G))
          ( comp-isometry-Pseudometric-Space
            ( cauchy-pseudocompletion-Metric-Ab G)
            ( cauchy-pseudocompletion-Metric-Ab G)
            ( pseudometric-Metric-Space
              ( metric-quotient-cauchy-pseudocompletion-Metric-Ab G))
            ( isometry-unit-metric-quotient-Pseudometric-Space
              ( cauchy-pseudocompletion-Metric-Ab G))
            ( isometry-cauchy-pseudocompletion-Metric-Space
              ( metric-space-Metric-Ab G)
              ( metric-space-Metric-Ab G)
              ( isometry-neg-Metric-Ab G)))
          ( d)
          ( x')
          ( y')
          ( reflects-neighborhoods-map-unit-metric-quotient-Pseudometric-Space
            ( cauchy-pseudocompletion-Metric-Ab G)
            ( d)
            ( x')
            ( y')
            ( binary-tr
              ( neighborhood-metric-quotient-cauchy-pseudocompletion-Metric-Ab
                ( G)
                ( d))
              ( inv ux'=x)
              ( inv uy'=y)
              ( Ndxy))))
```

### Left addition is a short map on the metric quotient of the Cauchy pseudocompletion of a metric abelian group

```agda
module _
  {l1 l2 : Level}
  (G : Metric-Ab l1 l2)
  where abstract

  is-short-map-left-add-metric-quotient-cauchy-pseudocompletion-Metric-Ab :
    (x : type-metric-quotient-cauchy-pseudocompletion-Metric-Ab G) →
    is-short-map-Metric-Space
      ( metric-quotient-cauchy-pseudocompletion-Metric-Ab G)
      ( metric-quotient-cauchy-pseudocompletion-Metric-Ab G)
      ( add-metric-quotient-cauchy-pseudocompletion-Metric-Ab G x)
  is-short-map-left-add-metric-quotient-cauchy-pseudocompletion-Metric-Ab
    x d y z Ndyz =
    let
      open
        do-syntax-trunc-Prop
          ( neighborhood-prop-metric-quotient-cauchy-pseudocompletion-Metric-Ab
            ( G)
            ( d)
            ( add-metric-quotient-cauchy-pseudocompletion-Metric-Ab G x y)
            ( add-metric-quotient-cauchy-pseudocompletion-Metric-Ab G x z))
    in do
      (x' , ux'=x) ←
        is-surjective-quotient-map
          ( equivalence-relation-sim-cauchy-pseudocompletion-Metric-Ab G)
          ( x)
      (y' , uy'=y) ←
        is-surjective-quotient-map
          ( equivalence-relation-sim-cauchy-pseudocompletion-Metric-Ab G)
          ( y)
      (z' , uz'=z) ←
        is-surjective-quotient-map
          ( equivalence-relation-sim-cauchy-pseudocompletion-Metric-Ab G)
          ( z)
      binary-tr
        ( neighborhood-metric-quotient-cauchy-pseudocompletion-Metric-Ab G d)
        ( ( inv
            ( add-in-approximation-metric-quotient-cauchy-pseudocompletion-Metric-Ab
              ( G)
              ( x')
              ( y'))) ∙
          ( ap-binary
            ( add-metric-quotient-cauchy-pseudocompletion-Metric-Ab G)
            ( ux'=x)
            ( uy'=y)))
        ( ( inv
            ( add-in-approximation-metric-quotient-cauchy-pseudocompletion-Metric-Ab
              ( G)
              ( x')
              ( z'))) ∙
          ( ap-binary
            ( add-metric-quotient-cauchy-pseudocompletion-Metric-Ab G)
            ( ux'=x)
            ( uz'=z)))
        ( is-short-map-short-map-Pseudometric-Space
          ( cauchy-pseudocompletion-Metric-Ab G)
          ( pseudometric-Metric-Space
            ( metric-quotient-cauchy-pseudocompletion-Metric-Ab G))
          ( comp-short-map-Pseudometric-Space
            ( cauchy-pseudocompletion-Metric-Ab G)
            ( cauchy-pseudocompletion-Metric-Ab G)
            ( pseudometric-Metric-Space
              ( metric-quotient-cauchy-pseudocompletion-Metric-Ab G))
            ( short-map-unit-metric-quotient-Pseudometric-Space
              ( cauchy-pseudocompletion-Metric-Ab G))
            ( short-map-left-add-cauchy-pseudocompletion-Metric-Ab G x'))
          ( d)
          ( y')
          ( z')
          ( reflects-neighborhoods-map-unit-metric-quotient-Pseudometric-Space
            ( cauchy-pseudocompletion-Metric-Ab G)
            ( d)
            ( y')
            ( z')
            ( binary-tr
              ( neighborhood-metric-quotient-cauchy-pseudocompletion-Metric-Ab
                ( G)
                ( d))
              ( inv uy'=y)
              ( inv uz'=z)
              ( Ndyz))))
```

## Definition

```agda
module _
  {l1 l2 : Level}
  (G : Metric-Ab l1 l2)
  where

  metric-ab-metric-quotient-cauchy-pseudocompletion-Metric-Ab :
    Metric-Ab (l1 ⊔ l2) (l1 ⊔ l2)
  metric-ab-metric-quotient-cauchy-pseudocompletion-Metric-Ab =
    ( ab-metric-quotient-cauchy-pseudocompletion-Metric-Ab G ,
      pseudometric-structure-Metric-Space
        ( metric-quotient-cauchy-pseudocompletion-Metric-Ab G) ,
      is-extensional-pseudometric-Metric-Space
        ( metric-quotient-cauchy-pseudocompletion-Metric-Ab G) ,
      is-short-map-neg-metric-quotient-cauchy-pseudocompletion-Metric-Ab G ,
      is-short-map-left-add-metric-quotient-cauchy-pseudocompletion-Metric-Ab G)
```

## Properties

### The embedding of the metric abelian group into the metric abelian group of the metric quotient of its Cauchy pseudocompletion is an Abelian group homomorphism

```agda
module _
  {l1 l2 : Level}
  (G : Metric-Ab l1 l2)
  where

  hom-in-metric-quotient-cauchy-pseudocompletion-Metric-Ab :
    hom-Ab
      ( ab-Metric-Ab G)
      ( ab-metric-quotient-cauchy-pseudocompletion-Metric-Ab G)
  hom-in-metric-quotient-cauchy-pseudocompletion-Metric-Ab =
    ( in-metric-quotient-cauchy-pseudocompletion-Metric-Ab G ,
      inv (add-in-metric-quotient-cauchy-pseudocompletion-Metric-Ab G _ _))
```
