# The metric pseudocompletion of a pseudometric space

```agda
module metric-spaces.metric-pseudocompletion-of-pseudometric-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.positive-rational-numbers
open import elementary-number-theory.strict-inequality-rational-numbers

open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.binary-relations
open import foundation.binary-transport
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.existential-quantification
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.set-quotients
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import metric-spaces.cauchy-approximations-metric-spaces
open import metric-spaces.cauchy-approximations-pseudometric-spaces
open import metric-spaces.complete-metric-spaces
open import metric-spaces.convergent-cauchy-approximations-metric-spaces
open import metric-spaces.isometries-pseudometric-spaces
open import metric-spaces.limits-of-cauchy-approximations-metric-spaces
open import metric-spaces.limits-of-cauchy-approximations-pseudometric-spaces
open import metric-spaces.metric-quotients-of-pseudometric-spaces
open import metric-spaces.metric-spaces
open import metric-spaces.pseudometric-completion-of-pseudometric-spaces
open import metric-spaces.pseudometric-spaces
open import metric-spaces.rational-neighborhood-relations
open import metric-spaces.similarity-of-elements-pseudometric-spaces
```

</details>

## Idea

Metric pseudocompletion of pseudometric spaces.

## Definition

### The metric pseudocompletion of a pseudometric space

```agda
module _
  {l1 l2 : Level} (P : Pseudometric-Space l1 l2)
  where

  metric-pseudocompletion-Pseudometric-Space :
    Metric-Space (l1 ⊔ l2) (l1 ⊔ l2)
  metric-pseudocompletion-Pseudometric-Space =
    metric-quotient-Pseudometric-Space
      ( pseudometric-completion-Pseudometric-Space P)

  pseudometric-metric-pseudocompletion-Pseudometric-Space :
    Pseudometric-Space (l1 ⊔ l2) (l1 ⊔ l2)
  pseudometric-metric-pseudocompletion-Pseudometric-Space =
    pseudometric-Metric-Space
      metric-pseudocompletion-Pseudometric-Space
```

## Properties

```agda
module _
  {l1 l2 : Level} (P : Pseudometric-Space l1 l2)
  ( u :
    cauchy-approximation-Metric-Space
      ( metric-pseudocompletion-Pseudometric-Space P))
  where

  is-convergent-has-lift-cauchy-approximation-metric-pseudocompletion-Pseudometric-Space :
    has-lift-cauchy-approximation-metric-quotient-Pseudometric-Space
      ( pseudometric-completion-Pseudometric-Space P)
      ( u) →
    is-convergent-cauchy-approximation-Metric-Space
      ( metric-pseudocompletion-Pseudometric-Space P)
      ( u)
  is-convergent-has-lift-cauchy-approximation-metric-pseudocompletion-Pseudometric-Space
    sim-lift =
    let
      open
        do-syntax-trunc-Prop
          ( is-convergent-prop-cauchy-approximation-Metric-Space
            ( metric-pseudocompletion-Pseudometric-Space P)
            ( u))
    in do
      ( v , u~[v]) ← sim-lift
      let
        ( lim-v , is-lim-v) =
          has-limit-cauchy-approximation-pseudometric-completion-Pseudometric-Space
            ( P)
            ( v)

        lim-u =
          map-metric-quotient-Pseudometric-Space
            ( pseudometric-completion-Pseudometric-Space P)
            ( lim-v)

        is-lim[v]-lim-u :
          is-limit-cauchy-approximation-Metric-Space
            ( metric-quotient-Pseudometric-Space
              ( pseudometric-completion-Pseudometric-Space P))
            ( map-metric-quotient-cauchy-approximation-Pseudometric-Space
              ( pseudometric-completion-Pseudometric-Space P)
              ( v))
            ( lim-u)
        is-lim[v]-lim-u =
          preserves-limit-map-metric-quotient-cauchy-approximation-Pseudometric-Space
            ( pseudometric-completion-Pseudometric-Space P)
            ( v)
            ( lim-v)
            ( is-lim-v)

        [lim-u] =
          const-cauchy-approximation-Metric-Space
            ( metric-pseudocompletion-Pseudometric-Space P)
            ( lim-u)

        u~[lim-u] :
          sim-Pseudometric-Space
            ( pseudometric-completion-Pseudometric-Space
              ( pseudometric-metric-pseudocompletion-Pseudometric-Space P))
            ( u)
            ( [lim-u])
        u~[lim-u] =
          transitive-sim-Pseudometric-Space
            ( pseudometric-completion-Pseudometric-Space
              ( pseudometric-metric-pseudocompletion-Pseudometric-Space P))
            ( u)
            ( map-metric-quotient-cauchy-approximation-Pseudometric-Space
              ( pseudometric-completion-Pseudometric-Space P)
              ( v))
            ( [lim-u])
            ( sim-const-is-limit-cauchy-approximation-Pseudometric-Space
              ( pseudometric-metric-pseudocompletion-Pseudometric-Space P)
              ( map-metric-quotient-cauchy-approximation-Pseudometric-Space
                ( pseudometric-completion-Pseudometric-Space P)
                ( v))
              ( lim-u)
              ( is-lim[v]-lim-u))
            ( u~[v])
      ( ( lim-u) ,
        ( is-limit-sim-const-cauchy-approximation-Pseudometric-Space
          ( pseudometric-metric-pseudocompletion-Pseudometric-Space P)
          ( u)
          ( lim-u)
          ( u~[lim-u])))

  iff-has-lift-is-convergent-cauchy-approximation-metric-pseudocompletion-Pseudometric-Space :
    is-convergent-cauchy-approximation-Metric-Space
      ( metric-pseudocompletion-Pseudometric-Space P)
      ( u) ↔
    has-lift-cauchy-approximation-metric-quotient-Pseudometric-Space
      ( pseudometric-completion-Pseudometric-Space P)
      ( u)
  pr1
    iff-has-lift-is-convergent-cauchy-approximation-metric-pseudocompletion-Pseudometric-Space
    =
    has-lift-is-convergent-cauchy-approximation-metric-quotient-Pseudometric-Space
      ( pseudometric-completion-Pseudometric-Space P)
      ( u)
  pr2
    iff-has-lift-is-convergent-cauchy-approximation-metric-pseudocompletion-Pseudometric-Space
    =
    is-convergent-has-lift-cauchy-approximation-metric-pseudocompletion-Pseudometric-Space

  equiv-has-lift-is-convergent-cauchy-approximation-metric-pseudocompletion-Pseudometric-Space :
    is-convergent-cauchy-approximation-Metric-Space
      ( metric-pseudocompletion-Pseudometric-Space P)
      ( u) ≃
    has-lift-cauchy-approximation-metric-quotient-Pseudometric-Space
      ( pseudometric-completion-Pseudometric-Space P)
      ( u)
  equiv-has-lift-is-convergent-cauchy-approximation-metric-pseudocompletion-Pseudometric-Space
    =
    equiv-iff
      ( is-convergent-prop-cauchy-approximation-Metric-Space
        ( metric-pseudocompletion-Pseudometric-Space P)
        ( u))
      ( has-lift-prop-cauchy-approximation-metric-quotient-Pseudometric-Space
        ( pseudometric-completion-Pseudometric-Space P)
        ( u))
      ( has-lift-is-convergent-cauchy-approximation-metric-quotient-Pseudometric-Space
        ( pseudometric-completion-Pseudometric-Space P)
        ( u))
      ( is-convergent-has-lift-cauchy-approximation-metric-pseudocompletion-Pseudometric-Space)
```

TO BE REMOVED. JUST HERE FOR EXPOSITORY PURPOSE.

```agda
module _
  {l1 l2 : Level} (P : Pseudometric-Space l1 l2)
  where

  lemma-is-convergent-cauchy-approximation-metric-pseudocompletion-Pseudometric-Space :
    ( u :
      cauchy-approximation-Metric-Space
        ( metric-pseudocompletion-Pseudometric-Space P)) →
    is-convergent-cauchy-approximation-Metric-Space
      ( metric-pseudocompletion-Pseudometric-Space P)
      ( u) ↔
    exists
      ( cauchy-approximation-Pseudometric-Space
        ( pseudometric-completion-Pseudometric-Space P))
      ( λ v →
        sim-prop-Pseudometric-Space
          ( pseudometric-completion-Pseudometric-Space
            ( pseudometric-metric-pseudocompletion-Pseudometric-Space P))
          ( u)
          ( map-metric-quotient-cauchy-approximation-Pseudometric-Space
            ( pseudometric-completion-Pseudometric-Space P)
            ( v)))
  lemma-is-convergent-cauchy-approximation-metric-pseudocompletion-Pseudometric-Space
    =
    iff-has-lift-is-convergent-cauchy-approximation-metric-pseudocompletion-Pseudometric-Space
      ( P)
```
