# Extensions of pseudometric spaces

```agda
module metric-spaces.extensions-pseudometric-spaces where
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

An
{{#concept "extension" Disambiguation="of a pseudometric space" Agda=extension-Pseudometric-Space}}
of a [pseudometric space](metric-spaces.pseudometric-spaces.md) `P`is a
pseudometric space `Q` together with an
[isometry](metric-spaces.isometries-pseudometric-spaces.md) `i : P → Q`.

## Definition

### Extensions of pseudometric spaces

```agda
module _
  {l1 l2 : Level}
  (l3 l4 : Level)
  (P : Pseudometric-Space l1 l2)
  where

  extension-Pseudometric-Space : UU (l1 ⊔ l2 ⊔ lsuc l3 ⊔ lsuc l4)
  extension-Pseudometric-Space =
    Σ ( Pseudometric-Space l3 l4)
      ( isometry-Pseudometric-Space P)

module _
  {l1 l2 l3 l4 : Level}
  (P : Pseudometric-Space l1 l2)
  (E : extension-Pseudometric-Space l3 l4 P)
  where

  pseudometric-space-extension-Pseudometric-Space : Pseudometric-Space l3 l4
  pseudometric-space-extension-Pseudometric-Space = pr1 E

  isometry-pseudometric-space-extension-Pseudometric-Space :
    isometry-Pseudometric-Space
      ( P)
      ( pseudometric-space-extension-Pseudometric-Space)
  isometry-pseudometric-space-extension-Pseudometric-Space = pr2 E

  map-isometry-pseudometric-space-extension-Pseudometric-Space :
    type-Pseudometric-Space P →
    type-Pseudometric-Space pseudometric-space-extension-Pseudometric-Space
  map-isometry-pseudometric-space-extension-Pseudometric-Space =
    map-isometry-Pseudometric-Space
      ( P)
      ( pseudometric-space-extension-Pseudometric-Space)
      ( isometry-pseudometric-space-extension-Pseudometric-Space)

  is-isometry-map-extension-Pseudometric-Space :
    is-isometry-Pseudometric-Space
      ( P)
      ( pseudometric-space-extension-Pseudometric-Space)
      ( map-isometry-pseudometric-space-extension-Pseudometric-Space)
  is-isometry-map-extension-Pseudometric-Space =
    is-isometry-map-isometry-Pseudometric-Space
      ( P)
      ( pseudometric-space-extension-Pseudometric-Space)
      ( isometry-pseudometric-space-extension-Pseudometric-Space)
```
