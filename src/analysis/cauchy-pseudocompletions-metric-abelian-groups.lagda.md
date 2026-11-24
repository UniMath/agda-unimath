# Cauchy pseudocompletions of metric abelian groups

```agda
module analysis.cauchy-pseudocompletions-metric-abelian-groups where
```

<details><summary>Imports</summary>

```agda
open import analysis.cauchy-approximations-metric-abelian-groups
open import analysis.metric-abelian-groups

open import elementary-number-theory.positive-rational-numbers

open import foundation.binary-relations
open import foundation.equivalence-relations
open import foundation.identity-types
open import foundation.universe-levels

open import metric-spaces.cauchy-pseudocompletions-of-metric-spaces
open import metric-spaces.pseudometric-spaces
open import metric-spaces.rational-neighborhood-relations
open import metric-spaces.similarity-of-elements-pseudometric-spaces
```

</details>

## Idea

The
{{#concept "Cauchy pseudocompletion" Disambiguation="of a metric abelian group" Agda=cauchy-pseudocompletion-Metric-Ab}}
of a [metric abelian group](analysis.metric-abelian-groups.md) is the
[Cauchy pseudocompletion](metric-spaces.cauchy-pseudocompletions-of-metric-spaces.md)
of the underlying [metric space](metric-spaces.metric-spaces.md).

## Definition

```agda
module _
  {l1 l2 : Level}
  (G : Metric-Ab l1 l2)
  where

  cauchy-pseudocompletion-Metric-Ab : Pseudometric-Space (l1 ⊔ l2) l2
  cauchy-pseudocompletion-Metric-Ab =
    cauchy-pseudocompletion-Metric-Space (metric-space-Metric-Ab G)

  neighborhood-prop-cauchy-pseudocompletion-Metric-Ab :
    Rational-Neighborhood-Relation l2 (cauchy-approximation-Metric-Ab G)
  neighborhood-prop-cauchy-pseudocompletion-Metric-Ab =
    neighborhood-prop-Pseudometric-Space cauchy-pseudocompletion-Metric-Ab

  neighborhood-cauchy-pseudocompletion-Metric-Ab :
    ℚ⁺ → Relation l2 (cauchy-approximation-Metric-Ab G)
  neighborhood-cauchy-pseudocompletion-Metric-Ab =
    neighborhood-Pseudometric-Space cauchy-pseudocompletion-Metric-Ab

  equivalence-relation-sim-cauchy-pseudocompletion-Metric-Ab :
    equivalence-relation l2 (cauchy-approximation-Metric-Ab G)
  equivalence-relation-sim-cauchy-pseudocompletion-Metric-Ab =
    equivalence-relation-sim-Pseudometric-Space
      ( cauchy-pseudocompletion-Metric-Ab)

  sim-prop-cauchy-pseudocompletion-Metric-Ab :
    Relation-Prop l2 (cauchy-approximation-Metric-Ab G)
  sim-prop-cauchy-pseudocompletion-Metric-Ab =
    sim-prop-Pseudometric-Space cauchy-pseudocompletion-Metric-Ab

  sim-cauchy-pseudocompletion-Metric-Ab :
    Relation l2 (cauchy-approximation-Metric-Ab G)
  sim-cauchy-pseudocompletion-Metric-Ab =
    sim-Pseudometric-Space cauchy-pseudocompletion-Metric-Ab
```

## Properties

### If two constant Cauchy approximations are similar, they have the same constant

```agda
module _
  {l1 l2 : Level}
  (G : Metric-Ab l1 l2)
  where abstract

  eq-sim-const-cauchy-approximation-cauchy-pseudocompletion-Metric-Ab :
    (x y : type-Metric-Ab G) →
    sim-cauchy-pseudocompletion-Metric-Ab G
      ( const-cauchy-approximation-Metric-Ab G x)
      ( const-cauchy-approximation-Metric-Ab G y) →
    x ＝ y
  eq-sim-const-cauchy-approximation-cauchy-pseudocompletion-Metric-Ab =
    eq-sim-const-cauchy-approximation-cauchy-pseudocompletion-Metric-Space
      ( metric-space-Metric-Ab G)
```
