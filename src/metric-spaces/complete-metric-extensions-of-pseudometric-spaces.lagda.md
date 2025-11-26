# Complete metric extensions of pseudometric spaces

```agda
module metric-spaces.complete-metric-extensions-of-pseudometric-spaces where
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
open import foundation.equality-dependent-pair-types
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
open import foundation.universe-levels

open import metric-spaces.cauchy-approximations-metric-quotients-of-pseudometric-spaces
open import metric-spaces.cauchy-approximations-metric-spaces
open import metric-spaces.cauchy-approximations-pseudometric-spaces
open import metric-spaces.cauchy-metric-extensions-of-pseudometric-spaces
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
open import metric-spaces.metric-extensions-of-pseudometric-spaces
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
{{#concept "complete metric extension" Disambiguation="of a pseudometric space" Agda=Complete-Metric-Extension}}
of a [pseudometric space](metric-spaces.pseudometric-spaces.md) is a
[metric extension](metric-spaces.metric-extensions-of-pseudometric-spaces.md)
such that the target [metric space](metric-spaces.metric-spaces.md) is
[complete](metric-spaces.complete-metric-spaces.md).

Any **complete metric extension** of a pseudometric space induces a metric
extension of its
[cauchy pseudocompletion](metric-spaces.cauchy-pseudocompletion-of-pseudometric-spaces.md)
hence a
[Cauchy metric extension](metric-spaces.cauchy-metric-extensions-of-pseudometric-spaces.md).

## Definitions

### The property of being a complete metric extension

```agda
module _
  {l1 l2 l3 l4 : Level}
  (P : Pseudometric-Space l1 l2)
  (M : Metric-Extension l3 l4 P)
  where

  is-complete-prop-Metric-Extension : Prop (l3 ⊔ l4)
  is-complete-prop-Metric-Extension =
    is-complete-prop-Metric-Space
      ( metric-space-Metric-Extension P M)

  is-complete-Metric-Extension : UU (l3 ⊔ l4)
  is-complete-Metric-Extension =
    type-Prop is-complete-prop-Metric-Extension

  is-prop-is-complete-Metric-Extension :
    is-prop is-complete-Metric-Extension
  is-prop-is-complete-Metric-Extension =
    is-prop-type-Prop is-complete-prop-Metric-Extension
```

### Complete metric extensions of pseudometric spaces

```agda
module _
  {l1 l2 : Level}
  (l3 l4 : Level)
  (P : Pseudometric-Space l1 l2)
  where

  Complete-Metric-Extension : UU (l1 ⊔ l2 ⊔ lsuc l3 ⊔ lsuc l4)
  Complete-Metric-Extension =
    Σ ( Metric-Extension l3 l4 P)
      ( is-complete-Metric-Extension P)

module _
  {l1 l2 l3 l4 : Level}
  (P : Pseudometric-Space l1 l2)
  (M : Complete-Metric-Extension l3 l4 P)
  where

  extension-Complete-Metric-Extension :
    Metric-Extension l3 l4 P
  extension-Complete-Metric-Extension = pr1 M

  metric-space-Complete-Metric-Extension : Metric-Space l3 l4
  metric-space-Complete-Metric-Extension =
    metric-space-Metric-Extension P extension-Complete-Metric-Extension

  pseudometric-space-Complete-Metric-Extension : Pseudometric-Space l3 l4
  pseudometric-space-Complete-Metric-Extension =
    pseudometric-space-Metric-Extension P extension-Complete-Metric-Extension

  is-complete-metric-space-Complete-Metric-Extension :
    is-complete-Metric-Space metric-space-Complete-Metric-Extension
  is-complete-metric-space-Complete-Metric-Extension = pr2 M

  complete-metric-space-Complete-Metric-Extension : Complete-Metric-Space l3 l4
  complete-metric-space-Complete-Metric-Extension =
    ( metric-space-Complete-Metric-Extension ,
      is-complete-metric-space-Complete-Metric-Extension)
```

## Properties

### Any complete metric extension induces a metric extension of the Cauchy pseudocompletion

```agda
module _
  {l1 l2 l3 l4 : Level}
  (P : Pseudometric-Space l1 l2)
  (M : Complete-Metric-Extension l3 l4 P)
  where

  isometry-cauchy-pseudocompletion-Complete-Metric-Extension :
    isometry-Pseudometric-Space
      ( cauchy-pseudocompletion-Pseudometric-Space P)
      ( pseudometric-space-Complete-Metric-Extension P M)
  isometry-cauchy-pseudocompletion-Complete-Metric-Extension =
    comp-isometry-Pseudometric-Space
      ( cauchy-pseudocompletion-Pseudometric-Space P)
      ( cauchy-pseudocompletion-Metric-Space
        ( metric-space-Complete-Metric-Extension P M))
      ( pseudometric-space-Complete-Metric-Extension P M)
      ( isometry-map-lim-cauchy-pseudocompletion-is-complete-Metric-Space
        ( metric-space-Complete-Metric-Extension P M)
        ( is-complete-metric-space-Complete-Metric-Extension P M))
      ( isometry-cauchy-pseudocompletion-Metric-Extension
        ( P)
        ( extension-Complete-Metric-Extension P M))

  extension-cauchy-pseudocompletion-Complete-Metric-Extension :
    Metric-Extension l3 l4 (cauchy-pseudocompletion-Pseudometric-Space P)
  extension-cauchy-pseudocompletion-Complete-Metric-Extension =
    ( metric-space-Complete-Metric-Extension P M ,
      isometry-cauchy-pseudocompletion-Complete-Metric-Extension)
```

### Any complete metric extension induces a Cauchy metric extension

```agda
module _
  {l1 l2 l3 l4 : Level}
  (P : Pseudometric-Space l1 l2)
  (M : Complete-Metric-Extension l3 l4 P)
  where

  cauchy-extension-Complete-Metric-Extension : Cauchy-Metric-Extension l3 l4 P
  cauchy-extension-Complete-Metric-Extension =
    cauchy-extension-cauchy-pseudocompletion-Metric-Extension P
      ( extension-cauchy-pseudocompletion-Complete-Metric-Extension P M)
```
