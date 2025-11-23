# Initial metric extensions of pseudometric spaces

```agda
{-# OPTIONS --lossy-unification #-}

module metric-spaces.initial-metric-extensions-of-pseudometric-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-positive-rational-numbers
open import elementary-number-theory.positive-rational-numbers

open import foundation.action-on-identifications-functions
open import foundation.binary-relations
open import foundation.binary-transport
open import foundation.contractible-maps
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equivalence-classes
open import foundation.equivalences
open import foundation.existential-quantification
open import foundation.fibers-of-maps
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.inhabited-subtypes
open import foundation.logical-equivalences
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.reflecting-maps-equivalence-relations
open import foundation.retractions
open import foundation.sections
open import foundation.set-quotients
open import foundation.sets
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.universal-property-set-quotients
open import foundation.universe-levels

open import logic.functoriality-existential-quantification

open import metric-spaces.cauchy-approximations-metric-spaces
open import metric-spaces.cauchy-approximations-pseudometric-spaces
open import metric-spaces.convergent-cauchy-approximations-metric-spaces
open import metric-spaces.equality-of-metric-spaces
open import metric-spaces.extensionality-pseudometric-spaces
open import metric-spaces.functions-metric-spaces
open import metric-spaces.isometries-between-metric-extensions-of-pseudometric-spaces
open import metric-spaces.isometries-metric-spaces
open import metric-spaces.isometries-pseudometric-spaces
open import metric-spaces.limits-of-cauchy-approximations-metric-spaces
open import metric-spaces.limits-of-cauchy-approximations-pseudometric-spaces
open import metric-spaces.metric-extensions-of-pseudometric-spaces
open import metric-spaces.metric-quotients-of-pseudometric-spaces
open import metric-spaces.metric-spaces
open import metric-spaces.pseudometric-spaces
open import metric-spaces.rational-neighborhood-relations
open import metric-spaces.short-functions-metric-spaces
open import metric-spaces.short-functions-pseudometric-spaces
open import metric-spaces.similarity-of-elements-pseudometric-spaces
```

</details>

## Idea

The [metric quotient](metric-spaces.metric-quotients-of-pseudometric-spaces.md)
of a [pseudometric space](metric-spaces.pseudometric-spaces.md) is the
{{concept "initial metric extension" Agda=initial-Metric-Extension}}: for any
metric extension `i : P → M` of a pseudometric space `P`, there exists a unique
[isometry of metric extensions](metric-spaces.isometries-between-metric-extensions-of-pseudometric-spaces.md)
`f : [P] → M`.

## Definitions

### The initial metric extension of a pseudometric space

```agda
module _
  {l1 l2 : Level}
  (P : Pseudometric-Space l1 l2)
  where

  initial-Metric-Extension : Metric-Extension (l1 ⊔ l2) (l1 ⊔ l2) P
  initial-Metric-Extension =
    ( metric-quotient-Pseudometric-Space P ,
      isometry-metric-quotient-Pseudometric-Space P)
```

## Properties

### The induced isometry from the metric quotient is an isometry of metric extensions

```agda
module _
  {l1 l2 l3 l4 : Level}
  (P : Pseudometric-Space l1 l2)
  (M : Metric-Extension l3 l4 P)
  where

  isometry-metric-space-initial-Metric-Extension :
    isometry-Metric-Space
      ( metric-quotient-Pseudometric-Space P)
      ( metric-space-Metric-Extension P M)
  isometry-metric-space-initial-Metric-Extension =
    isometry-map-isometry-metric-quotient-Pseudometric-Space
      ( P)
      ( metric-space-Metric-Extension P M)
      ( isometry-metric-space-Metric-Extension P M)

  coh-initial-Metric-Extension :
    coherence-triangle-isometry-metric-space-Metric-Extension
      ( P)
      ( initial-Metric-Extension P)
      ( M)
      ( isometry-metric-space-initial-Metric-Extension)
  coh-initial-Metric-Extension x =
    compute-map-isometry-metric-quotient-Pseudometric-Space
      ( P)
      ( metric-space-Metric-Extension P M)
      ( isometry-metric-space-Metric-Extension P M)
      ( map-metric-quotient-Pseudometric-Space P x)
      ( x)
      ( is-in-class-map-quotient-Pseudometric-Space P x)

  isometry-initial-Metric-Extension :
    isometry-Metric-Extension
      ( P)
      ( initial-Metric-Extension P)
      ( M)
  isometry-initial-Metric-Extension =
    ( isometry-metric-space-initial-Metric-Extension ,
      coh-initial-Metric-Extension)
```

### The metric quotient is the initial metric extension

```agda
module _
  { l1 l2 l3 l4 : Level}
  ( P : Pseudometric-Space l1 l2)
  ( M : Metric-Extension l3 l4 P)
  ( f :
    isometry-Metric-Extension
      ( P)
      ( initial-Metric-Extension P)
      ( M))
  where abstract

  all-htpy-isometry-initial-Metric-Extension :
    htpy-isometry-Metric-Extension
      ( P)
      ( initial-Metric-Extension P)
      ( M)
      ( isometry-initial-Metric-Extension P M)
      ( f)
  all-htpy-isometry-initial-Metric-Extension X =
    let
      map-ext =
        map-isometry-metric-quotient-Pseudometric-Space
          ( P)
          ( metric-space-Metric-Extension P M)
          ( isometry-metric-space-Metric-Extension P M)

      map-f =
        map-metric-space-isometry-Metric-Extension
          ( P)
          ( initial-Metric-Extension P)
          ( M)
          ( f)

      open
        do-syntax-trunc-Prop
          ( eq-prop-Metric-Space
            ( metric-space-Metric-Extension P M)
            ( map-ext X)
            ( map-f X))

      in do
        ( x , x∈X) ←
          is-inhabited-class-metric-quotient-Pseudometric-Space P X

        let
          lemma-lhs =
            compute-map-isometry-metric-quotient-Pseudometric-Space
              ( P)
              ( metric-space-Metric-Extension P M)
              ( isometry-metric-space-Metric-Extension P M)
              ( X)
              ( x)
              ( x∈X)

          lemma-mhs =
            coh-isometry-Metric-Extension
              ( P)
              ( initial-Metric-Extension P)
              ( M)
              ( f)
              ( x)

          lemma-rhs =
            ap
              ( map-metric-space-isometry-Metric-Extension
                ( P)
                ( initial-Metric-Extension P)
                ( M)
                ( f))
              ( eq-map-is-in-class-metric-quotient-Pseudometric-Space
                ( P)
                ( X)
                ( x∈X))

        lemma-lhs ∙ (inv lemma-mhs) ∙ lemma-rhs

  contraction-isometry-initial-Metric-Extension :
    isometry-initial-Metric-Extension P M ＝ f
  contraction-isometry-initial-Metric-Extension =
    eq-htpy-isometry-Metric-Extension
      ( P)
      ( initial-Metric-Extension P)
      ( M)
      ( isometry-initial-Metric-Extension P M)
      ( f)
      ( all-htpy-isometry-initial-Metric-Extension)

module _
  { l1 l2 l3 l4 : Level}
  ( P : Pseudometric-Space l1 l2)
  ( M : Metric-Extension l3 l4 P)
  where abstract

  is-contr-isometry-initial-Metric-Extension :
    is-contr
      ( isometry-Metric-Extension
        ( P)
        ( initial-Metric-Extension P)
        ( M))
  is-contr-isometry-initial-Metric-Extension =
    ( isometry-initial-Metric-Extension P M ,
      contraction-isometry-initial-Metric-Extension P M)
```
