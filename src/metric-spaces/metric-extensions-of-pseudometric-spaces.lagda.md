# Metric extensions of pseudometric spaces

```agda
module metric-spaces.metric-extensions-of-pseudometric-spaces where
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

A
{{#concept "metric extension" Disambiguation="of a pseudometric space" Agda=Metric-Extension}}
of a [pseudometric space](metric-spaces.pseudometric-spaces.md) `P` is a
[metric space](metric-spaces.metric-spaces.md) `M` together with an
[isometry](metric-spaces.isometries-pseudometric-spaces.md) `f : P → M`.

## Definition

### Metric extensions of pseudometric spaces

```agda
module _
  {l1 l2 : Level} (l3 l4 : Level) (P : Pseudometric-Space l1 l2)
  where

  Metric-Extension : UU (l1 ⊔ l2 ⊔ lsuc l3 ⊔ lsuc l4)
  Metric-Extension =
    Σ ( Metric-Space l3 l4)
      ( isometry-Pseudometric-Space P ∘ pseudometric-Metric-Space)
```

```agda
module _
  {l1 l2 l3 l4 : Level} (P : Pseudometric-Space l1 l2)
  (M : Metric-Extension l3 l4 P)
  where

  metric-space-Metric-Extension : Metric-Space l3 l4
  metric-space-Metric-Extension = pr1 M

  pseudometric-space-Metric-Extension : Pseudometric-Space l3 l4
  pseudometric-space-Metric-Extension =
    pseudometric-Metric-Space metric-space-Metric-Extension

  type-metric-space-Metric-Extension : UU l3
  type-metric-space-Metric-Extension =
    type-Metric-Space metric-space-Metric-Extension

  isometry-metric-space-Metric-Extension :
    isometry-Pseudometric-Space P pseudometric-space-Metric-Extension
  isometry-metric-space-Metric-Extension = pr2 M

  map-isometry-metric-space-Metric-Extension :
    type-Pseudometric-Space P → type-metric-space-Metric-Extension
  map-isometry-metric-space-Metric-Extension =
    map-isometry-Pseudometric-Space
      ( P)
      ( pseudometric-space-Metric-Extension)
      ( isometry-metric-space-Metric-Extension)
```

## Properties

### Action of metric extensions on Cauchy approximations

```agda
module _
  {l1 l2 l3 l4 : Level} (P : Pseudometric-Space l1 l2)
  (M : Metric-Extension l3 l4 P)
  where

  isometry-cauchy-pseudocompletion-Metric-Extension :
    isometry-Pseudometric-Space
      ( cauchy-pseudocompletion-Pseudometric-Space P)
      ( cauchy-pseudocompletion-Metric-Space
        ( metric-space-Metric-Extension P M))
  isometry-cauchy-pseudocompletion-Metric-Extension =
    isometry-map-cauchy-approximation-isometry-Pseudometric-Space
      ( P)
      ( pseudometric-space-Metric-Extension P M)
      ( isometry-metric-space-Metric-Extension P M)

  map-cauchy-pseudocompletion-Metric-Extension :
    cauchy-approximation-Pseudometric-Space P →
    cauchy-approximation-Metric-Space
      ( metric-space-Metric-Extension P M)
  map-cauchy-pseudocompletion-Metric-Extension =
    map-isometry-Pseudometric-Space
      ( cauchy-pseudocompletion-Pseudometric-Space P)
      ( cauchy-pseudocompletion-Metric-Space
        ( metric-space-Metric-Extension P M))
      ( isometry-cauchy-pseudocompletion-Metric-Extension)

  is-isometry-map-cauchy-pseudocompletion-Metric-Extension :
    is-isometry-Pseudometric-Space
      ( cauchy-pseudocompletion-Pseudometric-Space P)
      ( cauchy-pseudocompletion-Metric-Space
        ( metric-space-Metric-Extension P M))
      ( map-cauchy-pseudocompletion-Metric-Extension)
  is-isometry-map-cauchy-pseudocompletion-Metric-Extension =
    is-isometry-map-isometry-Pseudometric-Space
      ( cauchy-pseudocompletion-Pseudometric-Space P)
      ( cauchy-pseudocompletion-Metric-Space
        ( metric-space-Metric-Extension P M))
      ( isometry-cauchy-pseudocompletion-Metric-Extension)
```

### The action of metric extensions on Cauchy approximations is natural w.r.t. Cauchy pseudocompletions

```agda
module _
  {l1 l2 l3 l4 : Level} (P : Pseudometric-Space l1 l2)
  (M : Metric-Extension l3 l4 P)
  where

  htpy-map-cauchy-pseudocompletion-Metric-Extension :
    ( map-cauchy-pseudocompletion-Metric-Extension P M ∘
      map-cauchy-pseudocompletion-Pseudometric-Space P) ~
    ( ( map-cauchy-pseudocompletion-Metric-Space
        ( metric-space-Metric-Extension P M)) ∘
      ( map-isometry-metric-space-Metric-Extension P M))
  htpy-map-cauchy-pseudocompletion-Metric-Extension x =
    eq-htpy-cauchy-approximation-Metric-Space
      ( metric-space-Metric-Extension P M)
      ( refl-htpy)
```

### Limit points in metric extensions

```agda
module _
  {l1 l2 l3 l4 : Level}
  (P : Pseudometric-Space l1 l2)
  (M : Metric-Extension l3 l4 P)
  (u : cauchy-approximation-Pseudometric-Space P)
  (y : type-metric-space-Metric-Extension P M)
  where

  is-limit-map-cauchy-pseudocompletion-prop-Metric-Extension : Prop l4
  is-limit-map-cauchy-pseudocompletion-prop-Metric-Extension =
    is-limit-cauchy-approximation-prop-Metric-Space
      ( metric-space-Metric-Extension P M)
      ( map-cauchy-pseudocompletion-Metric-Extension P M u)
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
  (M : Metric-Extension l3 l4 P)
  (u v : cauchy-approximation-Pseudometric-Space P)
  (y : type-metric-space-Metric-Extension P M)
  where

  sim-has-same-limit-map-cauchy-pseudocompletion-Metric-Extension :
    is-limit-map-cauchy-pseudocompletion-Metric-Extension P M u y →
    is-limit-map-cauchy-pseudocompletion-Metric-Extension P M v y →
    sim-Pseudometric-Space
      ( cauchy-pseudocompletion-Pseudometric-Space P)
      ( u)
      ( v)
  sim-has-same-limit-map-cauchy-pseudocompletion-Metric-Extension lim-u lim-v =
    reflects-sim-map-isometry-Pseudometric-Space
      ( cauchy-pseudocompletion-Pseudometric-Space P)
      ( cauchy-pseudocompletion-Metric-Space
        ( metric-space-Metric-Extension P M))
      ( isometry-cauchy-pseudocompletion-Metric-Extension P M)
      ( u)
      ( v)
      ( sim-has-same-limit-cauchy-approximation-Pseudometric-Space
        ( pseudometric-space-Metric-Extension P M)
        ( map-cauchy-pseudocompletion-Metric-Extension P M u)
        ( map-cauchy-pseudocompletion-Metric-Extension P M v)
        ( y)
        ( lim-u)
        ( lim-v))

  has-same-limit-map-cauchy-sim-pseudocompletion-Metric-Extension :
    sim-Pseudometric-Space
      ( cauchy-pseudocompletion-Pseudometric-Space P)
      ( u)
      ( v) →
    is-limit-map-cauchy-pseudocompletion-Metric-Extension P M u y →
    is-limit-map-cauchy-pseudocompletion-Metric-Extension P M v y
  has-same-limit-map-cauchy-sim-pseudocompletion-Metric-Extension u~v =
    has-same-limit-sim-cauchy-approximation-Pseudometric-Space
      ( pseudometric-space-Metric-Extension P M)
      ( map-cauchy-pseudocompletion-Metric-Extension P M u)
      ( map-cauchy-pseudocompletion-Metric-Extension P M v)
      ( y)
      ( preserves-sim-map-isometry-Pseudometric-Space
        ( cauchy-pseudocompletion-Pseudometric-Space P)
        ( cauchy-pseudocompletion-Metric-Space
          ( metric-space-Metric-Extension P M))
        ( isometry-cauchy-pseudocompletion-Metric-Extension P M)
        ( u)
        ( v)
        ( u~v))
```
