# Limit points of extensions of metric spaces

```agda
module metric-spaces.limit-points-extensions-metric-spaces where
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

open import metric-spaces.action-on-cauchy-approximations-extensions-metric-spaces
open import metric-spaces.cauchy-approximations-metric-quotients-of-pseudometric-spaces
open import metric-spaces.cauchy-approximations-metric-spaces
open import metric-spaces.cauchy-approximations-pseudometric-spaces
open import metric-spaces.cauchy-pseudocompletion-of-metric-spaces
open import metric-spaces.cauchy-pseudocompletion-of-pseudometric-spaces
open import metric-spaces.complete-metric-spaces
open import metric-spaces.convergent-cauchy-approximations-metric-spaces
open import metric-spaces.equality-of-metric-spaces
open import metric-spaces.extensions-metric-spaces
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

Given an [extension of metric space](metric-spaces.extensions-metric-spaces.md)
`i : M → N`, a point `y : N` is called a
{{#concept "limit point" Disambiguation="of a metric extension" Agda=is-limit-prop-point-extension-Metric-Space}}
if there [exists](foundation.existential-quantification.md) a
[Cauchy approximation](metric-spaces.cauchy-approximations-metric-spaces.md) in
`M` whose image under the
[action of metric extensions](metric-spaces.action-on-cauchy-approximations-extensions-metric-spaces.md)
has [limit](metric-spaces.limits-of-cauchy-approximations-metric-spaces.md) `y`
in `N`.

## Definition

### Limit points in metric extensions

```agda
module _
  {l1 l2 l3 l4 : Level}
  (M : Metric-Space l1 l2)
  (E : extension-Metric-Space l3 l4 M)
  (y : type-metric-space-extension-Metric-Space M E)
  where

  is-limit-map-cauchy-pseudocompletion-prop-extension-Metric-Space :
    cauchy-approximation-Metric-Space M → Prop l4
  is-limit-map-cauchy-pseudocompletion-prop-extension-Metric-Space u =
    is-limit-cauchy-approximation-prop-Metric-Space
      ( metric-space-extension-Metric-Space M E)
      ( map-cauchy-approximation-extension-Metric-Space M E u)
      ( y)

  is-limit-map-cauchy-pseudocompletion-extension-Metric-Space :
    cauchy-approximation-Metric-Space M → UU l4
  is-limit-map-cauchy-pseudocompletion-extension-Metric-Space =
    type-Prop ∘ is-limit-map-cauchy-pseudocompletion-prop-extension-Metric-Space

  is-prop-is-limit-map-cauchy-pseudocompletion-extension-Metric-Space :
    (u : cauchy-approximation-Metric-Space M) →
    is-prop (is-limit-map-cauchy-pseudocompletion-extension-Metric-Space u)
  is-prop-is-limit-map-cauchy-pseudocompletion-extension-Metric-Space =
    is-prop-type-Prop ∘
    is-limit-map-cauchy-pseudocompletion-prop-extension-Metric-Space

  is-limit-prop-point-extension-Metric-Space : Prop (l1 ⊔ l2 ⊔ l4)
  is-limit-prop-point-extension-Metric-Space =
    ∃ ( cauchy-approximation-Metric-Space M)
      ( is-limit-map-cauchy-pseudocompletion-prop-extension-Metric-Space)

  is-limit-point-extension-Metric-Space : UU (l1 ⊔ l2 ⊔ l4)
  is-limit-point-extension-Metric-Space =
    type-Prop is-limit-prop-point-extension-Metric-Space

  is-prop-is-limit-point-extension-Metric-Space :
    is-prop is-limit-point-extension-Metric-Space
  is-prop-is-limit-point-extension-Metric-Space =
    is-prop-type-Prop is-limit-prop-point-extension-Metric-Space
```

## Properties

### Similarity in the Cauchy pseudocompletion of a pseudometric space preserves and reflects limits in a metric extension

```agda
module _
  {l1 l2 l3 l4 : Level}
  (M : Metric-Space l1 l2)
  (E : extension-Metric-Space l3 l4 M)
  (y : type-metric-space-extension-Metric-Space M E)
  (u v : cauchy-approximation-Metric-Space M)
  where

  sim-has-same-limit-map-cauchy-pseudocompletion-extension-Metric-Space :
    is-limit-map-cauchy-pseudocompletion-extension-Metric-Space M E y u →
    is-limit-map-cauchy-pseudocompletion-extension-Metric-Space M E y v →
    sim-Pseudometric-Space
      ( cauchy-pseudocompletion-Metric-Space M)
      ( u)
      ( v)
  sim-has-same-limit-map-cauchy-pseudocompletion-extension-Metric-Space
    lim-u lim-v =
    reflects-sim-map-isometry-Pseudometric-Space
      ( cauchy-pseudocompletion-Metric-Space M)
      ( cauchy-pseudocompletion-Metric-Space
        ( metric-space-extension-Metric-Space M E))
      ( isometry-cauchy-pseudocompletion-extension-Metric-Space M E)
      ( u)
      ( v)
      ( sim-has-same-limit-cauchy-approximation-Pseudometric-Space
        ( pseudometric-space-extension-Metric-Space M E)
        ( map-cauchy-approximation-extension-Metric-Space M E u)
        ( map-cauchy-approximation-extension-Metric-Space M E v)
        ( y)
        ( lim-u)
        ( lim-v))

  has-same-limit-map-cauchy-sim-pseudocompletion-extension-Metric-Space :
    sim-Pseudometric-Space
      ( cauchy-pseudocompletion-Metric-Space M)
      ( u)
      ( v) →
    is-limit-map-cauchy-pseudocompletion-extension-Metric-Space M E y u →
    is-limit-map-cauchy-pseudocompletion-extension-Metric-Space M E y v
  has-same-limit-map-cauchy-sim-pseudocompletion-extension-Metric-Space u~v =
    has-same-limit-sim-cauchy-approximation-Pseudometric-Space
      ( pseudometric-space-extension-Metric-Space M E)
      ( map-cauchy-approximation-extension-Metric-Space M E u)
      ( map-cauchy-approximation-extension-Metric-Space M E v)
      ( y)
      ( preserves-sim-map-isometry-Pseudometric-Space
        ( cauchy-pseudocompletion-Metric-Space M)
        ( cauchy-pseudocompletion-Metric-Space
          ( metric-space-extension-Metric-Space M E))
        ( isometry-cauchy-pseudocompletion-extension-Metric-Space M E)
        ( u)
        ( v)
        ( u~v))
```
