# The Cauchy precompletion of a metric space

```agda
{-# OPTIONS --lossy-unification #-}

module metric-spaces.cauchy-precompletions-metric-spaces where
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
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import logic.functoriality-existential-quantification

open import metric-spaces.action-on-cauchy-approximations-isometries-pseudometric-spaces
open import metric-spaces.action-on-cauchy-approximations-short-maps-pseudometric-spaces
open import metric-spaces.cauchy-approximations-cauchy-precompletions-pseudometric-spaces
open import metric-spaces.cauchy-approximations-in-cauchy-pseudocompletions-of-pseudometric-spaces
open import metric-spaces.cauchy-approximations-metric-quotients-of-pseudometric-spaces
open import metric-spaces.cauchy-approximations-metric-spaces
open import metric-spaces.cauchy-approximations-pseudometric-spaces
open import metric-spaces.cauchy-dense-extensions-metric-spaces
open import metric-spaces.cauchy-precompletions-cauchy-pseudocompletions-pseudometric-spaces
open import metric-spaces.cauchy-precompletions-pseudometric-spaces
open import metric-spaces.cauchy-pseudocompletion-of-complete-metric-spaces
open import metric-spaces.cauchy-pseudocompletion-of-metric-spaces
open import metric-spaces.cauchy-pseudocompletion-of-pseudometric-spaces
open import metric-spaces.complete-metric-spaces
open import metric-spaces.convergent-cauchy-approximations-metric-spaces
open import metric-spaces.equality-of-metric-spaces
open import metric-spaces.extensions-metric-spaces
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
open import metric-spaces.precomplete-extensions-metric-spaces
open import metric-spaces.pseudometric-spaces
open import metric-spaces.rational-neighborhood-relations
open import metric-spaces.short-functions-metric-spaces
open import metric-spaces.short-functions-pseudometric-spaces
open import metric-spaces.similarity-of-elements-pseudometric-spaces
```

</details>

## Idea

The
{{#concept "Cauchy precompletion" Disambiguation="of a metric space" Agda=cauchy-precompletion-Metric-Space}}
of a [metric space](metric-spaces.metric-spaces.md) `M` is the
[Cauchy precompletion](metric-spaces.cauchy-precompletions-pseudometric-spaces.md)
of its underlying [pseudometric space](metric-spaces.pseudometric-spaces.md),
i.e. the
[metric quotient](metric-spaces.metric-quotients-of-pseudometric-spaces.md) of
its
[Cauchy pseudocompletion](metric-spaces.cauchy-pseudocompletion-of-metric-spaces.md).

## Definition

### The Cauchy precompletion of a metric space

```agda
module _
  {l1 l2 : Level} (M : Metric-Space l1 l2)
  where

  cauchy-precompletion-Metric-Space :
    Metric-Space (l1 ⊔ l2) (l1 ⊔ l2)
  cauchy-precompletion-Metric-Space =
    metric-quotient-Pseudometric-Space
      ( cauchy-pseudocompletion-Metric-Space M)

  pseudometric-cauchy-precompletion-Metric-Space :
    Pseudometric-Space (l1 ⊔ l2) (l1 ⊔ l2)
  pseudometric-cauchy-precompletion-Metric-Space =
    pseudometric-Metric-Space
      cauchy-precompletion-Metric-Space

  type-cauchy-precompletion-Metric-Space : UU (l1 ⊔ l2)
  type-cauchy-precompletion-Metric-Space =
    type-Metric-Space cauchy-precompletion-Metric-Space
```

### The Cauchy precompletion of the Cauchy pseudocompletion of a metric space

```agda
module _
  {l1 l2 : Level} (M : Metric-Space l1 l2)
  where

  cauchy-precompletion-cauchy-pseudocompletion-Metric-Space :
    Metric-Space (l1 ⊔ l2) (l1 ⊔ l2)
  cauchy-precompletion-cauchy-pseudocompletion-Metric-Space =
    cauchy-precompletion-Pseudometric-Space
      ( cauchy-pseudocompletion-Metric-Space M)
```

## Properties

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

  map-isometry-cauchy-precompletion-cauchy-pseudocompletion-Metric-Space :
    cauchy-approximation-Metric-Space M →
    type-cauchy-precompletion-Metric-Space M
  map-isometry-cauchy-precompletion-cauchy-pseudocompletion-Metric-Space =
    map-isometry-Pseudometric-Space
      ( cauchy-pseudocompletion-Metric-Space M)
      ( pseudometric-cauchy-precompletion-Metric-Space M)
      ( isometry-cauchy-precompletion-cauchy-pseudocompletion-Metric-Space)

  extension-cauchy-precompletion-cauchy-pseudocompletion-Metric-Space :
    extension-Pseudometric-Space
      ( l1 ⊔ l2)
      ( l1 ⊔ l2)
      ( cauchy-pseudocompletion-Metric-Space M)
  pr1 extension-cauchy-precompletion-cauchy-pseudocompletion-Metric-Space =
    pseudometric-cauchy-precompletion-Metric-Space M
  pr2 extension-cauchy-precompletion-cauchy-pseudocompletion-Metric-Space =
    isometry-cauchy-precompletion-cauchy-pseudocompletion-Metric-Space
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

  map-isometry-cauchy-precompletion-Metric-Space :
    type-Metric-Space M →
    type-cauchy-precompletion-Metric-Space M
  map-isometry-cauchy-precompletion-Metric-Space =
    map-isometry-Metric-Space
      ( M)
      ( cauchy-precompletion-Metric-Space M)
      ( isometry-cauchy-precompletion-Metric-Space)

  extension-cauchy-precompletion-Metric-Space :
    extension-Metric-Space (l1 ⊔ l2) (l1 ⊔ l2) M
  pr1 extension-cauchy-precompletion-Metric-Space =
    cauchy-precompletion-Metric-Space M
  pr2 extension-cauchy-precompletion-Metric-Space =
    isometry-cauchy-precompletion-Metric-Space
```

### The equality between the Cauchy precompletion of the Cauchy pseudocompletion of a metric space and its Cauchy precompletion

```agda
module _
  {l1 l2 : Level} (M : Metric-Space l1 l2)
  where

  eq-cauchy-precompletion-pseudocompletion-Metric-Space :
    ( cauchy-precompletion-cauchy-pseudocompletion-Metric-Space M) ＝
    ( cauchy-precompletion-Metric-Space M)
  eq-cauchy-precompletion-pseudocompletion-Metric-Space =
    eq-cauchy-precompletion-pseudocompletion-Pseudometric-Space
      ( pseudometric-Metric-Space M)
```

### The Cauchy precompletion of a metric space is a precomplete extension of metric spaces

```agda
module _
  {l1 l2 : Level} (M : Metric-Space l1 l2)
  where

  is-precomplete-extension-cauchy-precompletion-Metric-Space :
    is-precomplete-extension-Metric-Space M
      ( extension-cauchy-precompletion-Metric-Space M)
  is-precomplete-extension-cauchy-precompletion-Metric-Space =
    is-convergent-map-isometry-cauchy-approximation-cauchy-precompletion-Pseudometric-Space
      ( pseudometric-Metric-Space M)
```

### Any precomplete extension of a metric space extends its Cauchy precompletion

```agda
module _
  {l1 l2 l3 l4 : Level}
  (M : Metric-Space l1 l2)
  (U : precomplete-extension-Metric-Space l3 l4 M)
  where

  isometry-cauchy-precompletion-precomplete-extension-Metric-Space :
    isometry-Metric-Space
      ( cauchy-precompletion-Metric-Space M)
      ( metric-space-precomplete-extension-Metric-Space M U)
  isometry-cauchy-precompletion-precomplete-extension-Metric-Space =
    isometry-map-isometry-metric-quotient-Pseudometric-Space
      ( cauchy-pseudocompletion-Metric-Space M)
      ( metric-space-precomplete-extension-Metric-Space M U)
      ( isometry-cauchy-pseudocompletion-precomplete-extension-Metric-Space M U)

  extension-cauchy-precompletion-precomplete-extension-Metric-Space :
    extension-Metric-Space l3 l4
      ( cauchy-precompletion-Metric-Space M)
  pr1 extension-cauchy-precompletion-precomplete-extension-Metric-Space =
    metric-space-precomplete-extension-Metric-Space M U
  pr2 extension-cauchy-precompletion-precomplete-extension-Metric-Space =
    isometry-cauchy-precompletion-precomplete-extension-Metric-Space
```

### The Cauchy precompletion of a metric space is a Cauchy-dense extension of metric spaces

```agda
module _
  {l1 l2 : Level} (M : Metric-Space l1 l2)
  where

  is-cauchy-dense-extension-cauchy-precompletion-Metric-Space :
    is-cauchy-dense-extension-Metric-Space M
      ( extension-cauchy-precompletion-Metric-Space M)
  is-cauchy-dense-extension-cauchy-precompletion-Metric-Space X =
    map-tot-exists
      ( is-limit-is-in-class-cauchy-precompletion-Pseudometric-Space
        ( pseudometric-Metric-Space M)
        ( X))
      ( is-inhabited-class-metric-quotient-Pseudometric-Space
        ( cauchy-pseudocompletion-Metric-Space M)
        ( X))
```
