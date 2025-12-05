# Metric extensions of pseudometric spaces

```agda
module metric-spaces.metric-extensions-pseudometric-spaces where
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
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.universe-levels

open import metric-spaces.action-on-cauchy-approximations-isometries-pseudometric-spaces
open import metric-spaces.cauchy-approximations-metric-quotients-of-pseudometric-spaces
open import metric-spaces.cauchy-approximations-metric-spaces
open import metric-spaces.cauchy-approximations-pseudometric-spaces
open import metric-spaces.cauchy-pseudocompletion-of-metric-spaces
open import metric-spaces.cauchy-pseudocompletion-of-pseudometric-spaces
open import metric-spaces.complete-metric-spaces
open import metric-spaces.convergent-cauchy-approximations-metric-spaces
open import metric-spaces.equality-of-metric-spaces
open import metric-spaces.extensionality-pseudometric-spaces
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

A
{{#concept "metric extension" Disambiguation="of a pseudometric space" Agda=metric-extension-Pseudometric-Space}}
of a [pseudometric space](metric-spaces.pseudometric-spaces.md) `P` is a
[metric space](metric-spaces.metric-spaces.md) `M` together with an
[isometry](metric-spaces.isometries-pseudometric-spaces.md) `f : P → M`.

This is equivalent to the type of
{{#concept "extensional extensions" Disambiguation="of a pseudometric space" Agda=extensional-extension-Pseudometric-Space}},
[extensions](metric-spaces.extensions-pseudometric-spaces.md) of pseudometric
spaces `i  : P → Q` such that `Q` is
[extensional](metric-spaces.extensionality-pseudometric-spaces.md).

## Definition

### Metric extensions of pseudometric spaces

```agda
module _
  {l1 l2 : Level} (l3 l4 : Level) (P : Pseudometric-Space l1 l2)
  where

  metric-extension-Pseudometric-Space : UU (l1 ⊔ l2 ⊔ lsuc l3 ⊔ lsuc l4)
  metric-extension-Pseudometric-Space =
    Σ ( Metric-Space l3 l4)
      ( isometry-Pseudometric-Space P ∘ pseudometric-Metric-Space)
```

```agda
module _
  {l1 l2 l3 l4 : Level} (P : Pseudometric-Space l1 l2)
  (M : metric-extension-Pseudometric-Space l3 l4 P)
  where

  metric-space-metric-extension-Pseudometric-Space : Metric-Space l3 l4
  metric-space-metric-extension-Pseudometric-Space = pr1 M

  pseudometric-space-metric-extension-Pseudometric-Space :
    Pseudometric-Space l3 l4
  pseudometric-space-metric-extension-Pseudometric-Space =
    pseudometric-Metric-Space metric-space-metric-extension-Pseudometric-Space

  type-metric-space-metric-extension-Pseudometric-Space : UU l3
  type-metric-space-metric-extension-Pseudometric-Space =
    type-Metric-Space metric-space-metric-extension-Pseudometric-Space

  isometry-metric-space-metric-extension-Pseudometric-Space :
    isometry-Pseudometric-Space
      ( P)
      ( pseudometric-space-metric-extension-Pseudometric-Space)
  isometry-metric-space-metric-extension-Pseudometric-Space = pr2 M

  map-isometry-metric-space-metric-extension-Pseudometric-Space :
    type-Pseudometric-Space P →
    type-metric-space-metric-extension-Pseudometric-Space
  map-isometry-metric-space-metric-extension-Pseudometric-Space =
    map-isometry-Pseudometric-Space
      ( P)
      ( pseudometric-space-metric-extension-Pseudometric-Space)
      ( isometry-metric-space-metric-extension-Pseudometric-Space)
```

### Extensional extensions of pseudometric spaces

```agda
module _
  {l1 l2 : Level}
  (l3 l4 : Level)
  (P : Pseudometric-Space l1 l2)
  where

  is-extensional-prop-extension-Pseudometric-Space :
    extension-Pseudometric-Space l3 l4 P → Prop (l3 ⊔ l4)
  is-extensional-prop-extension-Pseudometric-Space M =
    is-extensional-prop-Pseudometric-Space
      ( pseudometric-space-extension-Pseudometric-Space P M)

  extensional-extension-Pseudometric-Space : UU (l1 ⊔ l2 ⊔ lsuc l3 ⊔ lsuc l4)
  extensional-extension-Pseudometric-Space =
    type-subtype
      (is-extensional-prop-extension-Pseudometric-Space)
```

## Properties

### Metric extensions are extensional extensions of pseudometric spaces

```agda
module _
  {l1 l2 l3 l4 : Level}
  (P : Pseudometric-Space l1 l2)
  where

  equiv-extensional-metric-extension-Pseudometric-Space :
    metric-extension-Pseudometric-Space l3 l4 P ≃
    extensional-extension-Pseudometric-Space l3 l4 P
  equiv-extensional-metric-extension-Pseudometric-Space =
    equiv-right-swap-Σ
```

### The forgetful metric extension of a metric space into itself

```agda
module _
  {l1 l2 : Level} (M : Metric-Space l1 l2)
  where

  forgetful-metric-extension-Pseudometric-Space :
    metric-extension-Pseudometric-Space l1 l2 (pseudometric-Metric-Space M)
  forgetful-metric-extension-Pseudometric-Space =
    (M , id-isometry-Metric-Space M)
```

### Action of metric extensions on Cauchy approximations

```agda
module _
  {l1 l2 l3 l4 : Level} (P : Pseudometric-Space l1 l2)
  (M : metric-extension-Pseudometric-Space l3 l4 P)
  where

  isometry-cauchy-pseudocompletion-metric-extension-Pseudometric-Space :
    isometry-Pseudometric-Space
      ( cauchy-pseudocompletion-Pseudometric-Space P)
      ( cauchy-pseudocompletion-Metric-Space
        ( metric-space-metric-extension-Pseudometric-Space P M))
  isometry-cauchy-pseudocompletion-metric-extension-Pseudometric-Space =
    isometry-map-cauchy-approximation-isometry-Pseudometric-Space
      ( P)
      ( pseudometric-space-metric-extension-Pseudometric-Space P M)
      ( isometry-metric-space-metric-extension-Pseudometric-Space P M)

  map-cauchy-pseudocompletion-metric-extension-Pseudometric-Space :
    cauchy-approximation-Pseudometric-Space P →
    cauchy-approximation-Metric-Space
      ( metric-space-metric-extension-Pseudometric-Space P M)
  map-cauchy-pseudocompletion-metric-extension-Pseudometric-Space =
    map-isometry-Pseudometric-Space
      ( cauchy-pseudocompletion-Pseudometric-Space P)
      ( cauchy-pseudocompletion-Metric-Space
        ( metric-space-metric-extension-Pseudometric-Space P M))
      ( isometry-cauchy-pseudocompletion-metric-extension-Pseudometric-Space)

  is-isometry-map-cauchy-pseudocompletion-metric-extension-Pseudometric-Space :
    is-isometry-Pseudometric-Space
      ( cauchy-pseudocompletion-Pseudometric-Space P)
      ( cauchy-pseudocompletion-Metric-Space
        ( metric-space-metric-extension-Pseudometric-Space P M))
      ( map-cauchy-pseudocompletion-metric-extension-Pseudometric-Space)
  is-isometry-map-cauchy-pseudocompletion-metric-extension-Pseudometric-Space =
    is-isometry-map-isometry-Pseudometric-Space
      ( cauchy-pseudocompletion-Pseudometric-Space P)
      ( cauchy-pseudocompletion-Metric-Space
        ( metric-space-metric-extension-Pseudometric-Space P M))
      ( isometry-cauchy-pseudocompletion-metric-extension-Pseudometric-Space)
```

### Limit points in metric extensions

```agda
module _
  {l1 l2 l3 l4 : Level}
  (P : Pseudometric-Space l1 l2)
  (M : metric-extension-Pseudometric-Space l3 l4 P)
  (u : cauchy-approximation-Pseudometric-Space P)
  (y : type-metric-space-metric-extension-Pseudometric-Space P M)
  where

  is-limit-map-cauchy-pseudocompletion-prop-metric-extension-Pseudometric-Space :
    Prop l4
  is-limit-map-cauchy-pseudocompletion-prop-metric-extension-Pseudometric-Space
    =
    is-limit-cauchy-approximation-prop-Metric-Space
      ( metric-space-metric-extension-Pseudometric-Space P M)
      ( map-cauchy-pseudocompletion-metric-extension-Pseudometric-Space P M u)
      ( y)

  is-limit-map-cauchy-pseudocompletion-metric-extension-Pseudometric-Space :
    UU l4
  is-limit-map-cauchy-pseudocompletion-metric-extension-Pseudometric-Space =
    type-Prop
      is-limit-map-cauchy-pseudocompletion-prop-metric-extension-Pseudometric-Space

  is-prop-is-limit-map-cauchy-pseudocompletion-metric-extension-Pseudometric-Space :
    is-prop
      is-limit-map-cauchy-pseudocompletion-metric-extension-Pseudometric-Space
  is-prop-is-limit-map-cauchy-pseudocompletion-metric-extension-Pseudometric-Space
    =
    is-prop-type-Prop
      is-limit-map-cauchy-pseudocompletion-prop-metric-extension-Pseudometric-Space
```

### Similarity in the Cauchy pseudocompletion of a pseudometric space preserves and reflects limits in a metric extension

```agda
module _
  {l1 l2 l3 l4 : Level}
  (P : Pseudometric-Space l1 l2)
  (M : metric-extension-Pseudometric-Space l3 l4 P)
  (u v : cauchy-approximation-Pseudometric-Space P)
  (y : type-metric-space-metric-extension-Pseudometric-Space P M)
  where

  sim-has-same-limit-map-cauchy-pseudocompletion-metric-extension-Pseudometric-Space :
    is-limit-map-cauchy-pseudocompletion-metric-extension-Pseudometric-Space
      P M u y →
    is-limit-map-cauchy-pseudocompletion-metric-extension-Pseudometric-Space
      P M v y →
    sim-Pseudometric-Space
      ( cauchy-pseudocompletion-Pseudometric-Space P)
      ( u)
      ( v)
  sim-has-same-limit-map-cauchy-pseudocompletion-metric-extension-Pseudometric-Space
    lim-u lim-v =
    reflects-sim-map-isometry-Pseudometric-Space
      ( cauchy-pseudocompletion-Pseudometric-Space P)
      ( cauchy-pseudocompletion-Metric-Space
        ( metric-space-metric-extension-Pseudometric-Space P M))
      ( isometry-cauchy-pseudocompletion-metric-extension-Pseudometric-Space
        P M)
      ( u)
      ( v)
      ( sim-has-same-limit-cauchy-approximation-Pseudometric-Space
        ( pseudometric-space-metric-extension-Pseudometric-Space P M)
        ( map-cauchy-pseudocompletion-metric-extension-Pseudometric-Space P M u)
        ( map-cauchy-pseudocompletion-metric-extension-Pseudometric-Space P M v)
        ( y)
        ( lim-u)
        ( lim-v))

  has-same-limit-map-cauchy-sim-pseudocompletion-metric-extension-Pseudometric-Space :
    sim-Pseudometric-Space
      ( cauchy-pseudocompletion-Pseudometric-Space P)
      ( u)
      ( v) →
    is-limit-map-cauchy-pseudocompletion-metric-extension-Pseudometric-Space
      P M u y →
    is-limit-map-cauchy-pseudocompletion-metric-extension-Pseudometric-Space
      P M v y
  has-same-limit-map-cauchy-sim-pseudocompletion-metric-extension-Pseudometric-Space
    u~v =
    has-same-limit-sim-cauchy-approximation-Pseudometric-Space
      ( pseudometric-space-metric-extension-Pseudometric-Space P M)
      ( map-cauchy-pseudocompletion-metric-extension-Pseudometric-Space P M u)
      ( map-cauchy-pseudocompletion-metric-extension-Pseudometric-Space P M v)
      ( y)
      ( preserves-sim-map-isometry-Pseudometric-Space
        ( cauchy-pseudocompletion-Pseudometric-Space P)
        ( cauchy-pseudocompletion-Metric-Space
          ( metric-space-metric-extension-Pseudometric-Space P M))
        ( isometry-cauchy-pseudocompletion-metric-extension-Pseudometric-Space
          P M)
        ( u)
        ( v)
        ( u~v))
```
