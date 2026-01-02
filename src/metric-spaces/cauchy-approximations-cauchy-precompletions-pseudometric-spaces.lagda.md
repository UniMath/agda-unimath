# Cauchy approximations in the Cauchy precompletion of a pseudometric space

```agda
{-# OPTIONS --lossy-unification #-}

module metric-spaces.cauchy-approximations-cauchy-precompletions-pseudometric-spaces where
```

<details><summary>Imports</summary>

```agda
open import category-theory.isomorphisms-in-precategories

open import elementary-number-theory.addition-positive-rational-numbers
open import elementary-number-theory.positive-rational-numbers
open import elementary-number-theory.strict-inequality-positive-rational-numbers
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
open import foundation.surjective-maps
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import logic.functoriality-existential-quantification

open import metric-spaces.action-on-cauchy-approximations-isometries-pseudometric-spaces
open import metric-spaces.action-on-cauchy-approximations-short-maps-pseudometric-spaces
open import metric-spaces.cauchy-approximations-in-cauchy-pseudocompletions-of-pseudometric-spaces
open import metric-spaces.cauchy-approximations-metric-quotients-of-pseudometric-spaces
open import metric-spaces.cauchy-approximations-metric-spaces
open import metric-spaces.cauchy-approximations-pseudometric-spaces
open import metric-spaces.cauchy-precompletions-pseudometric-spaces
open import metric-spaces.cauchy-pseudocompletion-of-complete-metric-spaces
open import metric-spaces.cauchy-pseudocompletion-of-metric-spaces
open import metric-spaces.cauchy-pseudocompletion-of-pseudometric-spaces
open import metric-spaces.complete-metric-spaces
open import metric-spaces.convergent-cauchy-approximations-metric-spaces
open import metric-spaces.equality-of-metric-spaces
open import metric-spaces.extensions-pseudometric-spaces
open import metric-spaces.functions-metric-spaces
open import metric-spaces.functions-pseudometric-spaces
open import metric-spaces.isometries-metric-spaces
open import metric-spaces.isometries-pseudometric-spaces
open import metric-spaces.limits-of-cauchy-approximations-metric-spaces
open import metric-spaces.limits-of-cauchy-approximations-pseudometric-spaces
open import metric-spaces.metric-quotients-of-pseudometric-spaces
open import metric-spaces.metric-spaces
open import metric-spaces.precategory-of-metric-spaces-and-short-functions
open import metric-spaces.pseudometric-spaces
open import metric-spaces.rational-neighborhood-relations
open import metric-spaces.short-functions-metric-spaces
open import metric-spaces.short-functions-pseudometric-spaces
open import metric-spaces.similarity-of-elements-pseudometric-spaces
```

</details>

## Idea

A [Cauchy approximation](metric-spaces.cauchy-approximations-metric-spaces.md)
`f : C [C M]` in the
[cauchy precompletion](metric-spaces.cauchy-precompletions-pseudometric-spaces.md)
`[C M]` of a [pseudometric space](metric-spaces.pseudometric-spaces.md) `M`, is
[convergent](metric-spaces.convergent-cauchy-approximations-metric-spaces.md) if
and only if it is
[similar](metric-spaces.similarity-of-elements-pseudometric-spaces.md) in
`C [C M]` to the
[pointwise quotient](metric-spaces.cauchy-approximations-metric-quotients-of-pseudometric-spaces.md)
of some
[Cauchy approximation](metric-spaces.cauchy-approximations-pseudometric-spaces.md)
`g : C (C M)`. In particular, the
[image](metric-spaces.action-on-cauchy-approximations-extensions-metric-spaces.md)
in `C [C M]` of any Cauchy approximation `u : C M` is convergent.

Moreover, the Cauchy precompletion of a pseudometric space is
[complete](metric-spaces.complete-metric-spaces.md) if and only if all its
Cauchy approximations have a lift up to similarity in its Cauchy
pseudocompletion.

## Properties

### A Cauchy approximation in the Cauchy precompletion of a pseudometric space is convergent if and only if it has a lift its Cauchy pseudocompletion

```agda
module _
  {l1 l2 : Level} (P : Pseudometric-Space l1 l2)
  ( u :
    cauchy-approximation-Metric-Space
      ( cauchy-precompletion-Pseudometric-Space P))
  where

  is-convergent-has-lift-cauchy-approximation-cauchy-precompletion-Pseudometric-Space :
    has-lift-cauchy-approximation-metric-quotient-Pseudometric-Space
      ( cauchy-pseudocompletion-Pseudometric-Space P)
      ( u) →
    is-convergent-cauchy-approximation-Metric-Space
      ( cauchy-precompletion-Pseudometric-Space P)
      ( u)
  is-convergent-has-lift-cauchy-approximation-cauchy-precompletion-Pseudometric-Space
    sim-lift =
    let
      open
        do-syntax-trunc-Prop
          ( is-convergent-prop-cauchy-approximation-Metric-Space
            ( cauchy-precompletion-Pseudometric-Space P)
            ( u))
    in do
      ( v , u~[v]) ← sim-lift
      let
        ( lim-v , is-lim-v) =
          has-limit-cauchy-approximation-cauchy-pseudocompletion-Pseudometric-Space
            ( P)
            ( v)

        lim-u =
          map-metric-quotient-Pseudometric-Space
            ( cauchy-pseudocompletion-Pseudometric-Space P)
            ( lim-v)

        is-lim[v]-lim-u :
          is-limit-cauchy-approximation-Metric-Space
            ( metric-quotient-Pseudometric-Space
              ( cauchy-pseudocompletion-Pseudometric-Space P))
            ( map-cauchy-approximation-metric-quotient-Pseudometric-Space
              ( cauchy-pseudocompletion-Pseudometric-Space P)
              ( v))
            ( lim-u)
        is-lim[v]-lim-u =
          preserves-limits-map-cauchy-approximation-metric-quotient-Pseudometric-Space
            ( cauchy-pseudocompletion-Pseudometric-Space P)
            ( v)
            ( lim-v)
            ( is-lim-v)

        [lim-u] =
          const-cauchy-approximation-Metric-Space
            ( cauchy-precompletion-Pseudometric-Space P)
            ( lim-u)

        u~[lim-u] :
          sim-Pseudometric-Space
            ( cauchy-pseudocompletion-Pseudometric-Space
              ( pseudometric-cauchy-precompletion-Pseudometric-Space P))
            ( u)
            ( [lim-u])
        u~[lim-u] =
          transitive-sim-Pseudometric-Space
            ( cauchy-pseudocompletion-Pseudometric-Space
              ( pseudometric-cauchy-precompletion-Pseudometric-Space P))
            ( u)
            ( map-cauchy-approximation-metric-quotient-Pseudometric-Space
              ( cauchy-pseudocompletion-Pseudometric-Space P)
              ( v))
            ( [lim-u])
            ( sim-const-is-limit-cauchy-approximation-Pseudometric-Space
              ( pseudometric-cauchy-precompletion-Pseudometric-Space P)
              ( map-cauchy-approximation-metric-quotient-Pseudometric-Space
                ( cauchy-pseudocompletion-Pseudometric-Space P)
                ( v))
              ( lim-u)
              ( is-lim[v]-lim-u))
            ( u~[v])
      ( ( lim-u) ,
        ( is-limit-sim-const-cauchy-approximation-Pseudometric-Space
          ( pseudometric-cauchy-precompletion-Pseudometric-Space P)
          ( u)
          ( lim-u)
          ( u~[lim-u])))

  iff-has-lift-is-convergent-cauchy-approximation-cauchy-precompletion-Pseudometric-Space :
    is-convergent-cauchy-approximation-Metric-Space
      ( cauchy-precompletion-Pseudometric-Space P)
      ( u) ↔
    has-lift-cauchy-approximation-metric-quotient-Pseudometric-Space
      ( cauchy-pseudocompletion-Pseudometric-Space P)
      ( u)
  pr1
    iff-has-lift-is-convergent-cauchy-approximation-cauchy-precompletion-Pseudometric-Space
    =
    has-lift-is-convergent-cauchy-approximation-metric-quotient-Pseudometric-Space
      ( cauchy-pseudocompletion-Pseudometric-Space P)
      ( u)
  pr2
    iff-has-lift-is-convergent-cauchy-approximation-cauchy-precompletion-Pseudometric-Space
    =
    is-convergent-has-lift-cauchy-approximation-cauchy-precompletion-Pseudometric-Space

  equiv-has-lift-is-convergent-cauchy-approximation-cauchy-precompletion-Pseudometric-Space :
    is-convergent-cauchy-approximation-Metric-Space
      ( cauchy-precompletion-Pseudometric-Space P)
      ( u) ≃
    has-lift-cauchy-approximation-metric-quotient-Pseudometric-Space
      ( cauchy-pseudocompletion-Pseudometric-Space P)
      ( u)
  equiv-has-lift-is-convergent-cauchy-approximation-cauchy-precompletion-Pseudometric-Space
    =
    equiv-iff
      ( is-convergent-prop-cauchy-approximation-Metric-Space
        ( cauchy-precompletion-Pseudometric-Space P)
        ( u))
      ( has-lift-prop-cauchy-approximation-metric-quotient-Pseudometric-Space
        ( cauchy-pseudocompletion-Pseudometric-Space P)
        ( u))
      ( has-lift-is-convergent-cauchy-approximation-metric-quotient-Pseudometric-Space
        ( cauchy-pseudocompletion-Pseudometric-Space P)
        ( u))
      ( is-convergent-has-lift-cauchy-approximation-cauchy-precompletion-Pseudometric-Space)
```

### Images of Cauchy approximations in a pseudometric space converge in its Cauchy precompletion

```agda
module _
  {l1 l2 : Level} (P : Pseudometric-Space l1 l2)
  (u : cauchy-approximation-Pseudometric-Space P)
  where

  is-convergent-map-isometry-cauchy-approximation-cauchy-precompletion-Pseudometric-Space :
    is-convergent-cauchy-approximation-Metric-Space
      ( cauchy-precompletion-Pseudometric-Space P)
      ( map-cauchy-approximation-isometry-Pseudometric-Space
        ( P)
        ( pseudometric-cauchy-precompletion-Pseudometric-Space P)
        ( isometry-cauchy-precompletion-Pseudometric-Space P)
        ( u))
  is-convergent-map-isometry-cauchy-approximation-cauchy-precompletion-Pseudometric-Space
    =
    is-convergent-has-lift-cauchy-approximation-cauchy-precompletion-Pseudometric-Space
      ( P)
      ( map-cauchy-approximation-isometry-Pseudometric-Space
        ( P)
        ( pseudometric-cauchy-precompletion-Pseudometric-Space P)
        ( isometry-cauchy-precompletion-Pseudometric-Space P)
        ( u))
      ( has-lift-map-quotient-cauchy-approximation-metric-quotient-Pseudometric-Space
        ( cauchy-pseudocompletion-Pseudometric-Space P)
        ( map-cauchy-approximation-isometry-Pseudometric-Space
          ( P)
          ( cauchy-pseudocompletion-Pseudometric-Space P)
          ( isometry-cauchy-pseudocompletion-Pseudometric-Space P)
          ( u)))

  lim-map-isometry-cauchy-approximation-cauchy-precompletion-Pseudometric-Space :
    type-cauchy-precompletion-Pseudometric-Space P
  lim-map-isometry-cauchy-approximation-cauchy-precompletion-Pseudometric-Space =
    pr1
      is-convergent-map-isometry-cauchy-approximation-cauchy-precompletion-Pseudometric-Space

  is-limit-lim-map-isometry-cauchy-approximation-cauchy-precompletion-Pseudometric-Space :
    is-limit-cauchy-approximation-Metric-Space
      ( cauchy-precompletion-Pseudometric-Space P)
      ( map-cauchy-approximation-isometry-Pseudometric-Space
        ( P)
        ( pseudometric-cauchy-precompletion-Pseudometric-Space P)
        ( isometry-cauchy-precompletion-Pseudometric-Space P)
        ( u))
      ( lim-map-isometry-cauchy-approximation-cauchy-precompletion-Pseudometric-Space)
  is-limit-lim-map-isometry-cauchy-approximation-cauchy-precompletion-Pseudometric-Space
    =
    pr2
      is-convergent-map-isometry-cauchy-approximation-cauchy-precompletion-Pseudometric-Space
```

### The Cauchy precompletion of a pseudometric space is complete if and only if all its Cauchy approximations have a lift in its Cauchy pseudocompletion

```agda
module _
  {l1 l2 : Level} (P : Pseudometric-Space l1 l2)
  where

  iff-all-has-lift-is-complete-cauchy-precompletion-Pseudometric-Space :
    is-complete-Metric-Space (cauchy-precompletion-Pseudometric-Space P) ↔
    ( ( u : cauchy-approximation-Metric-Space
        ( cauchy-precompletion-Pseudometric-Space P)) →
      has-lift-cauchy-approximation-metric-quotient-Pseudometric-Space
        ( cauchy-pseudocompletion-Pseudometric-Space P)
        ( u))
  pr1 iff-all-has-lift-is-complete-cauchy-precompletion-Pseudometric-Space H u =
    has-lift-is-convergent-cauchy-approximation-metric-quotient-Pseudometric-Space
      ( cauchy-pseudocompletion-Pseudometric-Space P)
      ( u)
      ( H u)
  pr2 iff-all-has-lift-is-complete-cauchy-precompletion-Pseudometric-Space K u =
    is-convergent-has-lift-cauchy-approximation-cauchy-precompletion-Pseudometric-Space
      ( P)
      ( u)
      ( K u)
```

### The limit in the Cauchy precompletion of a Cauchy approximation in a Pseudometric space is its quotient

```agda
module _
  {l1 l2 : Level} (P : Pseudometric-Space l1 l2)
  (u : cauchy-approximation-Pseudometric-Space P)
  where

  eq-map-quotient-lim-map-isometry-cauchy-approximation-cauchy-precompletion-Pseudometric-Space :
    ( lim-map-isometry-cauchy-approximation-cauchy-precompletion-Pseudometric-Space
      ( P)
      ( u)) ＝
    ( map-metric-quotient-Pseudometric-Space
        ( cauchy-pseudocompletion-Pseudometric-Space P)
        ( u))
  eq-map-quotient-lim-map-isometry-cauchy-approximation-cauchy-precompletion-Pseudometric-Space
    =
    all-eq-is-limit-cauchy-approximation-Metric-Space
      ( cauchy-precompletion-Pseudometric-Space P)
      ( map-cauchy-approximation-isometry-Pseudometric-Space
        ( P)
        ( pseudometric-cauchy-precompletion-Pseudometric-Space P)
        ( isometry-cauchy-precompletion-Pseudometric-Space P)
        ( u))
      ( lim-map-isometry-cauchy-approximation-cauchy-precompletion-Pseudometric-Space
        ( P)
        ( u))
      ( map-metric-quotient-Pseudometric-Space
        ( cauchy-pseudocompletion-Pseudometric-Space P)
        ( u))
      ( is-limit-lim-map-isometry-cauchy-approximation-cauchy-precompletion-Pseudometric-Space
        ( P)
        ( u))
      ( is-limit-map-isometry-cauchy-pseudocompletion-cauchy-precompletion-Pseudometric-Space
        ( P)
        ( u))
```
