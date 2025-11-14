# The Cauchy precompletion of a metric space

```agda
{-# OPTIONS --lossy-unification #-}

module metric-spaces.cauchy-precompletion-of-metric-spaces where
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

open import metric-spaces.cauchy-approximations-metric-quotients-of-pseudometric-spaces
open import metric-spaces.cauchy-approximations-metric-spaces
open import metric-spaces.cauchy-approximations-pseudometric-spaces
open import metric-spaces.cauchy-precompletion-of-pseudometric-spaces
open import metric-spaces.cauchy-pseudocompletion-of-metric-spaces
open import metric-spaces.cauchy-pseudocompletion-of-pseudometric-spaces
open import metric-spaces.complete-metric-spaces
open import metric-spaces.convergent-cauchy-approximations-metric-spaces
open import metric-spaces.equality-of-metric-spaces
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

The
{{#concept "Cauchy precompletion" Disambiguation="of a metric space Agda=cauchy-precompletion-Metric-Space}}
of a [metric space](metric-spaces.metric-spaces.md) `M` is the
[Cauchy precompletion](metric-spaces.cauchy-precompletion-of-pseudometric-spaces.md)
of its underlying [pseudometric space](metric-spaces.pseudometric-spaces.md),
i.e., the
[metric quotient](metric-spaces.metric-quotients-of-pseudometric-spaces.md)
`[C M]` of its
[Cauchy pseudocompletion](metric-spaces.cauchy-pseudocompletion-of-metric-spaces.md)
`C M`.

The natural [isometry](metric-spaces.isometries-metric-spaces.md)

```text
M → [C M]
```

is an [equivalence](foundation.equivalences.md) if and only if `M` is
[complete](metric-spaces.complete-metric-spaces.md).

Any [short map](metric-spaces.short-functions-metric-spaces.md) (resp.
[isometry](metric-spaces.isometries-metric-spaces.md)) from a metric space in a
[complete metric space](metric-spaces.complete-metric-spaces.md) factors as a
short map (resp. isometry) through the Cauchy precompletion of its domain. This
is the
{{#concept "universal property" Disambiguation="of the Cauchy precompletion of a metric space"}}
of the Cauchy precompletion.

## Definitions

### The Cauchy precompletion of a metric space

```agda
module _
  {l1 l2 : Level} (M : Metric-Space l1 l2)
  where

  cauchy-precompletion-Metric-Space :
    Metric-Space (l1 ⊔ l2) (l1 ⊔ l2)
  cauchy-precompletion-Metric-Space =
    cauchy-precompletion-Pseudometric-Space
      ( pseudometric-Metric-Space M)

  pseudometric-cauchy-precompletion-Metric-Space :
    Pseudometric-Space (l1 ⊔ l2) (l1 ⊔ l2)
  pseudometric-cauchy-precompletion-Metric-Space =
    pseudometric-Metric-Space
      cauchy-precompletion-Metric-Space

  type-cauchy-precompletion-Metric-Space : UU (l1 ⊔ l2)
  type-cauchy-precompletion-Metric-Space =
    type-Metric-Space cauchy-precompletion-Metric-Space
```

### The isometry from the Cauchy pseudocompletion of a metric space into its Cauchy precompletion

```agda
module _
  {l1 l2 : Level} (M : Metric-Space l1 l2)
  where

  isometry-cauchy-precompletion-cauchy-pseudocompletion-Metric-Space :
    isometry-Pseudometric-Space
      ( cauchy-pseudocompletion-Metric-Space M)
      ( pseudometric-cauchy-precompletion-Metric-Space M)
  isometry-cauchy-precompletion-cauchy-pseudocompletion-Metric-Space =
    isometry-cauchy-precompletion-cauchy-pseudocompletion-Pseudometric-Space
      ( pseudometric-Metric-Space M)

  map-cauchy-precompletion-cauchy-pseudocompletion-Metric-Space :
    type-function-Pseudometric-Space
      ( cauchy-pseudocompletion-Metric-Space M)
      ( pseudometric-cauchy-precompletion-Metric-Space M)
  map-cauchy-precompletion-cauchy-pseudocompletion-Metric-Space =
    map-isometry-Pseudometric-Space
      ( cauchy-pseudocompletion-Metric-Space M)
      ( pseudometric-cauchy-precompletion-Metric-Space M)
      ( isometry-cauchy-precompletion-cauchy-pseudocompletion-Metric-Space)
```

### The isometry from a metric space into its Cauchy precompletion

```agda
module _
  {l1 l2 : Level} (M : Metric-Space l1 l2)
  where

  isometry-cauchy-precompletion-Metric-Space :
    isometry-Metric-Space
      ( M)
      ( cauchy-precompletion-Metric-Space M)
  isometry-cauchy-precompletion-Metric-Space =
    isometry-cauchy-precompletion-Pseudometric-Space
      ( pseudometric-Metric-Space M)

  map-cauchy-precompletion-Metric-Space :
    type-function-Metric-Space
      ( M)
      ( cauchy-precompletion-Metric-Space M)
  map-cauchy-precompletion-Metric-Space =
    map-isometry-Metric-Space
      ( M)
      ( cauchy-precompletion-Metric-Space M)
      ( isometry-cauchy-precompletion-Metric-Space)

  is-isometry-map-cauchy-precompletion-Metric-Space :
    is-isometry-Metric-Space
      ( M)
      ( cauchy-precompletion-Metric-Space M)
      ( map-cauchy-precompletion-Metric-Space)
  is-isometry-map-cauchy-precompletion-Metric-Space =
    is-isometry-map-isometry-Metric-Space
      ( M)
      ( cauchy-precompletion-Metric-Space M)
      ( isometry-cauchy-precompletion-Metric-Space)
```

## Properties

### The mapping from a complete metric space into its Cauchy precompletion is an isometric equivalence

```agda
module _
  {l1 l2 : Level} (M : Metric-Space l1 l2)
  (is-complete-M : is-complete-Metric-Space M)
  where

  short-map-lim-cauchy-precompletion-is-complete-Metric-Space :
    short-function-Metric-Space
      ( cauchy-precompletion-Metric-Space M)
      ( M)
  short-map-lim-cauchy-precompletion-is-complete-Metric-Space =
    short-map-short-function-metric-quotient-Pseudometric-Space
      ( cauchy-pseudocompletion-Metric-Space M)
      ( M)
      ( short-map-lim-cauchy-pseudocompletion-is-complete-Metric-Space
        ( M)
        ( is-complete-M))

  map-lim-cauchy-precompletion-is-complete-Metric-Space :
    type-function-Metric-Space
      ( cauchy-precompletion-Metric-Space M)
      ( M)
  map-lim-cauchy-precompletion-is-complete-Metric-Space =
    map-short-function-Metric-Space
      ( cauchy-precompletion-Metric-Space M)
      ( M)
      ( short-map-lim-cauchy-precompletion-is-complete-Metric-Space)

  compute-map-lim-cauchy-precompletion-is-complete-Metric-Space :
    (X : type-cauchy-precompletion-Metric-Space M) →
    (x : cauchy-approximation-Metric-Space M) →
    is-in-class-metric-quotient-Pseudometric-Space
      ( cauchy-pseudocompletion-Metric-Space M)
      ( X)
      ( x) →
    map-lim-cauchy-precompletion-is-complete-Metric-Space X ＝
    limit-cauchy-approximation-Complete-Metric-Space
      ( M , is-complete-M)
      ( x)
  compute-map-lim-cauchy-precompletion-is-complete-Metric-Space =
    compute-map-short-function-metric-quotient-Pseudometric-Space
      ( cauchy-pseudocompletion-Metric-Space M)
      ( M)
      ( short-map-lim-cauchy-pseudocompletion-is-complete-Metric-Space
        ( M)
        (is-complete-M))

  abstract
    is-section-map-cauchy-precompletion-is-complete-Metric-Space :
      ( map-cauchy-precompletion-Metric-Space M ∘
        map-lim-cauchy-precompletion-is-complete-Metric-Space) ~
      ( id)
    is-section-map-cauchy-precompletion-is-complete-Metric-Space U =
        let
          open
            do-syntax-trunc-Prop
              ( Id-Prop
                ( set-Metric-Space
                  ( cauchy-precompletion-Metric-Space M))
              ( map-cauchy-precompletion-Metric-Space M
                ( map-lim-cauchy-precompletion-is-complete-Metric-Space U))
              ( U))
          in do
            (u , u∈U) ←
              is-inhabited-class-metric-quotient-Pseudometric-Space
                ( cauchy-pseudocompletion-Metric-Space M)
                ( U)
            let
              lim-u : type-Metric-Space M
              lim-u =
                limit-cauchy-approximation-Complete-Metric-Space
                  ( M , is-complete-M)
                  ( u)

              compute-map-lim-U :
                map-lim-cauchy-precompletion-is-complete-Metric-Space U ＝ lim-u
              compute-map-lim-U =
                compute-map-lim-cauchy-precompletion-is-complete-Metric-Space
                  ( U)
                  ( u)
                  ( u∈U)

              sim-u-lim-u :
                sim-Pseudometric-Space
                  ( cauchy-pseudocompletion-Metric-Space M)
                  ( u)
                  ( const-cauchy-approximation-Metric-Space
                    ( M)
                    ( lim-u))
              sim-u-lim-u =
                sim-const-is-limit-cauchy-approximation-Metric-Space
                  ( M)
                  ( u)
                  ( lim-u)
                  ( is-limit-map-lim-cauchy-pseudocompletion-is-complete-Metric-Space
                    ( M)
                    ( is-complete-M)
                    ( u))

              [u]=[lim-u] :
                ( map-metric-quotient-Pseudometric-Space
                  ( cauchy-pseudocompletion-Metric-Space M)
                  ( u)) ＝
                ( map-cauchy-precompletion-Metric-Space M lim-u)
              [u]=[lim-u] =
                apply-effectiveness-quotient-map'
                  ( equivalence-relation-sim-Pseudometric-Space
                    ( cauchy-pseudocompletion-Metric-Space M))
                  ( sim-u-lim-u)

            ( ( ap
                ( map-cauchy-precompletion-Metric-Space M)
                ( compute-map-lim-U)) ∙
              ( inv [u]=[lim-u]) ∙
              ( eq-set-quotient-equivalence-class-set-quotient
                ( equivalence-relation-sim-Pseudometric-Space
                ( cauchy-pseudocompletion-Metric-Space M))
                ( U)
                ( u∈U)))

    is-retraction-map-cauchy-precompletion-is-complete-Metric-Space :
      ( map-lim-cauchy-precompletion-is-complete-Metric-Space ∘
        map-cauchy-precompletion-Metric-Space M) ~
      ( id)
    is-retraction-map-cauchy-precompletion-is-complete-Metric-Space x =
      ( compute-map-lim-cauchy-precompletion-is-complete-Metric-Space
        ( map-cauchy-precompletion-Metric-Space M x)
        ( const-cauchy-approximation-Metric-Space M x)
        ( is-in-class-map-quotient-Pseudometric-Space
          ( cauchy-pseudocompletion-Metric-Space M)
          ( const-cauchy-approximation-Metric-Space M x))) ∙
      ( is-retraction-limit-cauchy-approximation-Complete-Metric-Space
        ( M , is-complete-M)
        ( x))

    is-equiv-map-cauchy-precompletion-is-complete-Metric-Space :
      is-equiv
        ( map-cauchy-precompletion-Metric-Space M)
    is-equiv-map-cauchy-precompletion-is-complete-Metric-Space =
      is-equiv-is-invertible
        ( map-lim-cauchy-precompletion-is-complete-Metric-Space)
        ( is-section-map-cauchy-precompletion-is-complete-Metric-Space)
        ( is-retraction-map-cauchy-precompletion-is-complete-Metric-Space)

  isometric-equiv-cauchy-precompletion-is-complete-Metric-Space' :
    isometric-equiv-Metric-Space'
      ( M)
      ( cauchy-precompletion-Metric-Space M)
  isometric-equiv-cauchy-precompletion-is-complete-Metric-Space' =
    ( map-cauchy-precompletion-Metric-Space M ,
      is-equiv-map-cauchy-precompletion-is-complete-Metric-Space ,
      is-isometry-map-cauchy-precompletion-Metric-Space M)
```

### If the mapping from a metric space into its Cauchy precompletion is an equivalence, the metric space is complete

```agda
module _
  {l1 l2 : Level} (M : Metric-Space l1 l2)
  where

  is-complete-is-equiv-map-cauchy-precompletion-Metric-Space :
    is-equiv (map-cauchy-precompletion-Metric-Space M) →
    is-complete-Metric-Space M
  is-complete-is-equiv-map-cauchy-precompletion-Metric-Space H u =
    (lim-u , is-limit-lim-u)
    where

    lim-u : type-Metric-Space M
    lim-u =
      map-inv-is-equiv
        ( H)
        ( map-cauchy-precompletion-cauchy-pseudocompletion-Metric-Space
          ( M)
          ( u))

    is-limit-lim-u :
      is-limit-cauchy-approximation-Metric-Space
        ( M)
        ( u)
        ( lim-u)
    is-limit-lim-u =
      is-limit-sim-const-cauchy-approximation-Metric-Space
        ( M)
        ( u)
        ( lim-u)
        ( apply-effectiveness-quotient-map
          ( equivalence-relation-sim-Pseudometric-Space
            ( cauchy-pseudocompletion-Metric-Space M))
          ( inv
            ( is-section-map-section-is-equiv
              ( H)
              ( map-cauchy-precompletion-cauchy-pseudocompletion-Metric-Space
                ( M)
                ( u)))))
```

### If the Cauchy precompletion of a metric space is complete, then it is its own Cauchy precompletion

```agda
module _
  {l1 l2 : Level} (M : Metric-Space l1 l2)
  (H : is-complete-Metric-Space (cauchy-precompletion-Metric-Space M))
  where

  eq-cauchy-precompletion-is-complete-cauchy-precompletion-Metric-Space :
    cauchy-precompletion-Metric-Space (cauchy-precompletion-Metric-Space M) ＝
    cauchy-precompletion-Metric-Space M
  eq-cauchy-precompletion-is-complete-cauchy-precompletion-Metric-Space =
    inv
      ( eq-isometric-equiv-Metric-Space'
        ( cauchy-precompletion-Metric-Space M)
        ( cauchy-precompletion-Metric-Space
          ( cauchy-precompletion-Metric-Space M))
        ( isometric-equiv-cauchy-precompletion-is-complete-Metric-Space'
          ( cauchy-precompletion-Metric-Space M)
          ( H)))
```

### The Cauchy precompletion of a metric space is complete if and only if all its Cauchy approximations have a lift in its Cauchy pseudocompletion

```agda
module _
  {l1 l2 : Level} (M : Metric-Space l1 l2)
  where

  iff-all-has-lift-is-complete-cauchy-precompletion-Metric-Space :
    is-complete-Metric-Space (cauchy-precompletion-Metric-Space M) ↔
    ( ( u : cauchy-approximation-Metric-Space
        ( cauchy-precompletion-Metric-Space M)) →
      has-lift-cauchy-approximation-metric-quotient-Pseudometric-Space
        ( cauchy-pseudocompletion-Metric-Space M)
        ( u))
  iff-all-has-lift-is-complete-cauchy-precompletion-Metric-Space =
    iff-all-has-lift-is-complete-cauchy-precompletion-Pseudometric-Space
      ( pseudometric-Metric-Space M)
```

### Induced short map from the Cauchy precompletion to a complete metric space

```agda
module _
  { l1 l2 l3 l4 : Level} (M : Metric-Space l1 l2)
  ( C : Complete-Metric-Space l3 l4)
  where

  short-map-short-function-complete-metric-space-cauchy-precompletion-Metric-Space :
    short-function-Metric-Space
      ( M)
      ( metric-space-Complete-Metric-Space C) →
    short-function-Metric-Space
      ( cauchy-precompletion-Metric-Space M)
        ( metric-space-Complete-Metric-Space C)
  short-map-short-function-complete-metric-space-cauchy-precompletion-Metric-Space
    =
    short-map-short-function-complete-metric-space-cauchy-precompletion-Pseudometric-Space
      ( pseudometric-Metric-Space M)
      ( C)
```

### Induced isometry from the Cauchy precompletion into a complete metric space

```agda
module _
  { l1 l2 l3 l4 : Level} (M : Metric-Space l1 l2)
  ( C : Complete-Metric-Space l3 l4)
  where

  isometry-map-isometry-complete-metric-space-cauchy-precompletion-Metric-Space :
    isometry-Metric-Space
      ( M)
      ( metric-space-Complete-Metric-Space C) →
    isometry-Metric-Space
      ( cauchy-precompletion-Metric-Space M)
      ( metric-space-Complete-Metric-Space C)
  isometry-map-isometry-complete-metric-space-cauchy-precompletion-Metric-Space
    =
    isometry-map-isometry-complete-metric-space-cauchy-precompletion-Pseudometric-Space
      ( pseudometric-Metric-Space M)
      ( C)
```
