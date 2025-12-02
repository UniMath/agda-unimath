# Metric extensions

```agda
module metric-spaces.metric-extensions where
```

<details><summary>Imports</summary>

```agda
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
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import metric-spaces.action-of-isometries-on-cauchy-approximations-pseudometric-spaces
open import metric-spaces.cauchy-approximations-metric-quotients-of-pseudometric-spaces
open import metric-spaces.cauchy-approximations-metric-spaces
open import metric-spaces.cauchy-approximations-pseudometric-spaces
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

A {{#concept "metric extension" Agda=Metric-Extension}} between a
[pseudometric space](metric-spaces.pseudometric-spaces.md) `P` and a
[metric space](metric-spaces.metric-spaces.md) `M` is an
[isometry](metric-spaces.isometries-pseudometric-spaces.md) `f : P → M` between
`P` and the underlying pseudometric space of `M`.

## Definition

### Metric extensions

```agda
module _
  {l1 l2 l3 l4 : Level}
  (P : Pseudometric-Space l1 l2)
  (M : Metric-Space l3 l4)
  where

  Metric-Extension : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  Metric-Extension =
    isometry-Pseudometric-Space P (pseudometric-Metric-Space M)

  map-Metric-Extension :
    Metric-Extension →
    type-Pseudometric-Space P →
    type-Metric-Space M
  map-Metric-Extension = pr1

  is-isometry-map-Metric-Extension :
    (f : Metric-Extension) →
    is-isometry-Pseudometric-Space
      ( P)
      ( pseudometric-Metric-Space M)
      ( map-Metric-Extension f)
  is-isometry-map-Metric-Extension = pr2
```

## Properties

### The forgetful metric extension of a metric space into itself

```agda
module _
  {l1 l2 : Level} (M : Metric-Space l1 l2)
  where

  forgetful-Metric-Extension :
    Metric-Extension (pseudometric-Metric-Space M) M
  forgetful-Metric-Extension = id-isometry-Metric-Space M
```

### Action of metric extensions on Cauchy approximations

```agda
module _
  {l1 l2 l3 l4 : Level}
  (P : Pseudometric-Space l1 l2)
  (M : Metric-Space l3 l4)
  (f : Metric-Extension P M)
  where

  isometry-cauchy-pseudocompletion-Metric-Extension :
    isometry-Pseudometric-Space
      ( cauchy-pseudocompletion-Pseudometric-Space P)
      ( cauchy-pseudocompletion-Metric-Space M)
  isometry-cauchy-pseudocompletion-Metric-Extension =
    isometry-map-cauchy-approximation-isometry-Pseudometric-Space
      ( P)
      ( pseudometric-Metric-Space M)
      ( f)

  map-cauchy-approximation-Metric-Extension :
    cauchy-approximation-Pseudometric-Space P →
    cauchy-approximation-Metric-Space M
  map-cauchy-approximation-Metric-Extension =
    map-isometry-Pseudometric-Space
      ( cauchy-pseudocompletion-Pseudometric-Space P)
      ( cauchy-pseudocompletion-Metric-Space M)
      ( isometry-cauchy-pseudocompletion-Metric-Extension)

  is-isometry-map-cauchy-approximation-Metric-Extension :
    is-isometry-Pseudometric-Space
      ( cauchy-pseudocompletion-Pseudometric-Space P)
      ( cauchy-pseudocompletion-Metric-Space M)
      ( map-cauchy-approximation-Metric-Extension)
  is-isometry-map-cauchy-approximation-Metric-Extension =
    is-isometry-map-isometry-Pseudometric-Space
      ( cauchy-pseudocompletion-Pseudometric-Space P)
      ( cauchy-pseudocompletion-Metric-Space M)
      ( isometry-cauchy-pseudocompletion-Metric-Extension)
```

### Limit points in metric extensions

```agda
module _
  {l1 l2 l3 l4 : Level}
  (P : Pseudometric-Space l1 l2)
  (M : Metric-Space l3 l4)
  (f : Metric-Extension P M)
  (u : cauchy-approximation-Pseudometric-Space P)
  (y : type-Metric-Space M)
  where

  is-limit-map-cauchy-pseudocompletion-prop-Metric-Extension : Prop l4
  is-limit-map-cauchy-pseudocompletion-prop-Metric-Extension =
    is-limit-cauchy-approximation-prop-Metric-Space
      ( M)
      ( map-cauchy-approximation-Metric-Extension P M f u)
      ( y)

  is-limit-map-cauchy-pseudocompletion-Metric-Extension : UU l4
  is-limit-map-cauchy-pseudocompletion-Metric-Extension =
    type-Prop
      is-limit-map-cauchy-pseudocompletion-prop-Metric-Extension

  is-prop-is-limit-map-cauchy-pseudocompletion-Metric-Extension :
    is-prop is-limit-map-cauchy-pseudocompletion-Metric-Extension
  is-prop-is-limit-map-cauchy-pseudocompletion-Metric-Extension =
    is-prop-type-Prop
      is-limit-map-cauchy-pseudocompletion-prop-Metric-Extension
```

### Similarity in the Cauchy pseudocompletion of a pseudometric space preserves and reflects limits in a metric extension

```agda
module _
  {l1 l2 l3 l4 : Level}
  (P : Pseudometric-Space l1 l2)
  (M : Metric-Space l3 l4)
  (f : Metric-Extension P M)
  (u v : cauchy-approximation-Pseudometric-Space P)
  (y : type-Metric-Space M)
  where

  sim-has-same-limit-map-cauchy-pseudocompletion-Metric-Extension :
    is-limit-map-cauchy-pseudocompletion-Metric-Extension P M f u y →
    is-limit-map-cauchy-pseudocompletion-Metric-Extension P M f v y →
    sim-Pseudometric-Space
      ( cauchy-pseudocompletion-Pseudometric-Space P)
      ( u)
      ( v)
  sim-has-same-limit-map-cauchy-pseudocompletion-Metric-Extension lim-u lim-v =
    reflects-sim-map-isometry-Pseudometric-Space
      ( cauchy-pseudocompletion-Pseudometric-Space P)
      ( cauchy-pseudocompletion-Metric-Space M)
      ( isometry-cauchy-pseudocompletion-Metric-Extension P M f)
      ( u)
      ( v)
      ( sim-has-same-limit-cauchy-approximation-Pseudometric-Space
        ( pseudometric-Metric-Space M)
        ( map-cauchy-approximation-Metric-Extension P M f u)
        ( map-cauchy-approximation-Metric-Extension P M f v)
        ( y)
        ( lim-u)
        ( lim-v))

  has-same-limit-map-cauchy-sim-pseudocompletion-Metric-Extension :
    sim-Pseudometric-Space
      ( cauchy-pseudocompletion-Pseudometric-Space P)
      ( u)
      ( v) →
    is-limit-map-cauchy-pseudocompletion-Metric-Extension P M f u y →
    is-limit-map-cauchy-pseudocompletion-Metric-Extension P M f v y
  has-same-limit-map-cauchy-sim-pseudocompletion-Metric-Extension u~v =
    has-same-limit-sim-cauchy-approximation-Pseudometric-Space
      ( pseudometric-Metric-Space M)
      ( map-cauchy-approximation-Metric-Extension P M f u)
      ( map-cauchy-approximation-Metric-Extension P M f v)
      ( y)
      ( preserves-sim-map-isometry-Pseudometric-Space
        ( cauchy-pseudocompletion-Pseudometric-Space P)
        ( cauchy-pseudocompletion-Metric-Space M)
        ( isometry-cauchy-pseudocompletion-Metric-Extension P M f)
        ( u)
        ( v)
        ( u~v))
```
