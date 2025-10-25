# Cauchy approximations in metric quotients of pseudometric spaces

```agda
{-# OPTIONS --lossy-unification #-}

module metric-spaces.cauchy-approximations-metric-quotients-of-pseudometric-spaces where
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
open import metric-spaces.cauchy-pseudocompletion-of-metric-spaces
open import metric-spaces.cauchy-pseudocompletion-of-pseudometric-spaces
open import metric-spaces.convergent-cauchy-approximations-metric-spaces
open import metric-spaces.equality-of-metric-spaces
open import metric-spaces.extensionality-pseudometric-spaces
open import metric-spaces.functions-metric-spaces
open import metric-spaces.isometries-metric-spaces
open import metric-spaces.isometries-pseudometric-spaces
open import metric-spaces.limits-of-cauchy-approximations-metric-spaces
open import metric-spaces.limits-of-cauchy-approximations-pseudometric-spaces
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

The pointwise [quotients](foundation.set-quotients.md) of
[Cauchy approximations](metric-spaces.cauchy-approximations-pseudometric-spaces.md)
by the
[similarity relation](metric-spaces.similarity-of-elements-pseudometric-spaces.md)
of the [pseudometric space](metric-spaces.pseudometric-spaces.md) are Cauchy
approximations in the
[metric quotient](metric-spaces.metric-quotients-of-pseudometric-spaces.md). A
Cauchy approximation in a the metric quotient of a pseudometric space has a
{{#concept "lift up to similarity" Agda=has-lift-cauchy-approximation-metric-quotient-Pseudometric-Space}}
if it is similar (in the
[Cauchy pseudocompletion](metric-spaces.cauchy-pseudocompletion-of-metric-spaces.md)
of the metric quotient) to the pointwise quotient of
[some](foundation.existential-quantification.md) Cauchy approximation in the
pseudometric space.

The pointwise quotient of Cauchy approximations preserves
[limits](metric-spaces.limits-of-cauchy-approximations-pseudometric-spaces.md).
The pointwise quotient of a Cauchy approximation has a lift. A Cauchy
approximation that admits a
[limit](metric-spaces.limits-of-cauchy-approximations-pseudometric-spaces.md)
has a lift.

## Definitions

### The pointwise quotient Cauchy approximation of a Cauchy approximation in a pseudometric space

```agda
module _
  {l1 l2 : Level} (M : Pseudometric-Space l1 l2)
  where

  map-metric-quotient-cauchy-approximation-Pseudometric-Space :
    cauchy-approximation-Pseudometric-Space M →
    cauchy-approximation-Metric-Space
      ( metric-quotient-Pseudometric-Space M)
  map-metric-quotient-cauchy-approximation-Pseudometric-Space =
    map-short-function-cauchy-approximation-Pseudometric-Space
      ( M)
      ( pseudometric-metric-quotient-Pseudometric-Space M)
      ( short-map-metric-quotient-Pseudometric-Space M)
```

### Lifts of Cauchy approximations in the quotient metric space up to similarity

```agda
module _
  { l1 l2 : Level} (A : Pseudometric-Space l1 l2)
  ( u :
    cauchy-approximation-Metric-Space
      ( metric-quotient-Pseudometric-Space A))
  ( v : cauchy-approximation-Pseudometric-Space A)
  where

  is-lift-quotient-prop-cauchy-approximation-Pseudometric-Space :
    Prop (l1 ⊔ l2)
  is-lift-quotient-prop-cauchy-approximation-Pseudometric-Space =
    sim-prop-Pseudometric-Space
      ( cauchy-pseudocompletion-Pseudometric-Space
        ( pseudometric-metric-quotient-Pseudometric-Space A))
      ( u)
      ( map-metric-quotient-cauchy-approximation-Pseudometric-Space A v)

  is-lift-quotient-cauchy-approximation-Pseudometric-Space : UU (l1 ⊔ l2)
  is-lift-quotient-cauchy-approximation-Pseudometric-Space =
    type-Prop is-lift-quotient-prop-cauchy-approximation-Pseudometric-Space

  is-prop-is-lift-quotient-cauchy-approximation-Pseudometric-Space :
    is-prop is-lift-quotient-cauchy-approximation-Pseudometric-Space
  is-prop-is-lift-quotient-cauchy-approximation-Pseudometric-Space =
    is-prop-type-Prop
      is-lift-quotient-prop-cauchy-approximation-Pseudometric-Space

module _
  {l1 l2 : Level} (A : Pseudometric-Space l1 l2)
  ( u :
    cauchy-approximation-Metric-Space
      ( metric-quotient-Pseudometric-Space A))
  where

  has-lift-prop-cauchy-approximation-metric-quotient-Pseudometric-Space :
    Prop (l1 ⊔ l2)
  has-lift-prop-cauchy-approximation-metric-quotient-Pseudometric-Space =
    ∃ ( cauchy-approximation-Pseudometric-Space A)
      ( is-lift-quotient-prop-cauchy-approximation-Pseudometric-Space A u)

  has-lift-cauchy-approximation-metric-quotient-Pseudometric-Space :
    UU (l1 ⊔ l2)
  has-lift-cauchy-approximation-metric-quotient-Pseudometric-Space =
    type-Prop
      has-lift-prop-cauchy-approximation-metric-quotient-Pseudometric-Space

  is-prop-has-lift-cauchy-approximation-metric-quotient-Pseudometric-Space :
    is-prop has-lift-cauchy-approximation-metric-quotient-Pseudometric-Space
  is-prop-has-lift-cauchy-approximation-metric-quotient-Pseudometric-Space =
    is-prop-type-Prop
      has-lift-prop-cauchy-approximation-metric-quotient-Pseudometric-Space
```

## Properties

### The pointwise quotient of Cauchy approximations in the quotient metric space preserves limits

```agda
module _
  {l1 l2 : Level} (M : Pseudometric-Space l1 l2)
  (u : cauchy-approximation-Pseudometric-Space M)
  (lim : type-Pseudometric-Space M)
  (is-lim :
    is-limit-cauchy-approximation-Pseudometric-Space M u lim)
  where

  preserves-limit-map-metric-quotient-cauchy-approximation-Pseudometric-Space :
    is-limit-cauchy-approximation-Metric-Space
      ( metric-quotient-Pseudometric-Space M)
      ( map-metric-quotient-cauchy-approximation-Pseudometric-Space M u)
      ( map-metric-quotient-Pseudometric-Space M lim)
  preserves-limit-map-metric-quotient-cauchy-approximation-Pseudometric-Space
    ε δ (x , x∈uε) (y , y∈lim) =
    let
      lim~y : sim-Pseudometric-Space M lim y
      lim~y =
        sim-is-in-equivalence-class-quotient-map-set-quotient
          ( equivalence-relation-sim-Pseudometric-Space M)
          ( lim)
          ( y)
          ( y∈lim)

      uε~x :
        sim-Pseudometric-Space M
          ( map-cauchy-approximation-Pseudometric-Space M u ε)
          ( x)
      uε~x =
        sim-is-in-equivalence-class-quotient-map-set-quotient
          ( equivalence-relation-sim-Pseudometric-Space M)
          ( map-cauchy-approximation-Pseudometric-Space M u ε)
          ( x)
          ( x∈uε)
    in
      preserves-neighborhood-sim-Pseudometric-Space
        ( M)
        ( uε~x)
        ( lim~y)
        ( ε +ℚ⁺ δ)
        ( is-lim ε δ)
```

### Pointwise quotients of Cauchy approximations have lifts

```agda
module _
  {l1 l2 : Level} (A : Pseudometric-Space l1 l2)
  (u : cauchy-approximation-Pseudometric-Space A)
  where

  has-lift-map-quotient-cauchy-approximation-metric-quotient-Pseudometric-Space :
    has-lift-cauchy-approximation-metric-quotient-Pseudometric-Space
      ( A)
      ( map-metric-quotient-cauchy-approximation-Pseudometric-Space A u)
  has-lift-map-quotient-cauchy-approximation-metric-quotient-Pseudometric-Space =
    unit-trunc-Prop
      ( u ,
        refl-sim-Pseudometric-Space
          ( cauchy-pseudocompletion-Pseudometric-Space
            ( pseudometric-metric-quotient-Pseudometric-Space A))
          ( map-metric-quotient-cauchy-approximation-Pseudometric-Space A u))
```

### Convergent Cauchy approximations in the quotient metric space have a lift up to similarity

```agda
module _
  {l1 l2 : Level} (A : Pseudometric-Space l1 l2)
  ( u :
    cauchy-approximation-Metric-Space
      ( metric-quotient-Pseudometric-Space A))
  ( lim : type-Metric-Space (metric-quotient-Pseudometric-Space A))
  ( is-lim :
    is-limit-cauchy-approximation-Metric-Space
      ( metric-quotient-Pseudometric-Space A)
      ( u)
      ( lim))
  where

  lemma-sim-lift-is-limit-cauchy-approximation-metric-quotient-Pseudometric-Space :
    (x : type-Pseudometric-Space A) →
    (is-in-class-metric-quotient-Pseudometric-Space A lim x) →
    is-lift-quotient-cauchy-approximation-Pseudometric-Space
      ( A)
      ( u)
      ( const-cauchy-approximation-Pseudometric-Space A x)
  lemma-sim-lift-is-limit-cauchy-approximation-metric-quotient-Pseudometric-Space
    x x∈lim =
    transitive-sim-Pseudometric-Space
      ( cauchy-pseudocompletion-Pseudometric-Space
        ( pseudometric-metric-quotient-Pseudometric-Space A))
      ( u)
      ( const-cauchy-approximation-Pseudometric-Space
        ( pseudometric-metric-quotient-Pseudometric-Space A)
        ( lim))
      ( const-cauchy-approximation-Pseudometric-Space
        ( pseudometric-metric-quotient-Pseudometric-Space A)
        ( map-metric-quotient-Pseudometric-Space A x))
      ( λ d α β →
        sim-eq-Pseudometric-Space
          ( pseudometric-metric-quotient-Pseudometric-Space A)
          ( lim)
          ( map-metric-quotient-Pseudometric-Space A x)
          ( inv
            ( eq-set-quotient-equivalence-class-set-quotient
              ( equivalence-relation-sim-Pseudometric-Space A)
              ( lim)
              ( x∈lim)))
          ( α +ℚ⁺ β +ℚ⁺ d))
      ( sim-const-is-limit-cauchy-approximation-Pseudometric-Space
        ( pseudometric-metric-quotient-Pseudometric-Space A)
        ( u)
        ( lim)
        ( is-lim))

module _
  {l1 l2 : Level} (A : Pseudometric-Space l1 l2)
  ( u :
    cauchy-approximation-Metric-Space
      ( metric-quotient-Pseudometric-Space A))
  where

  has-lift-is-convergent-cauchy-approximation-metric-quotient-Pseudometric-Space :
    is-convergent-cauchy-approximation-Metric-Space
      ( metric-quotient-Pseudometric-Space A)
      ( u) →
    has-lift-cauchy-approximation-metric-quotient-Pseudometric-Space A u
  has-lift-is-convergent-cauchy-approximation-metric-quotient-Pseudometric-Space
    (lim , is-lim) =
    map-exists
      ( is-lift-quotient-cauchy-approximation-Pseudometric-Space A u)
      ( const-cauchy-approximation-Pseudometric-Space A)
      ( lemma-sim-lift-is-limit-cauchy-approximation-metric-quotient-Pseudometric-Space
        ( A)
        ( u)
        ( lim)
        ( is-lim))
      ( is-inhabited-class-metric-quotient-Pseudometric-Space A lim)
```
