# Metric quotients of Cauchy pseudocompletions of metric abelian groups

```agda
{-# OPTIONS --lossy-unification #-}

module analysis.metric-quotients-cauchy-pseudocompletions-metric-abelian-groups where
```

<details><summary>Imports</summary>

```agda
open import analysis.cauchy-approximations-metric-abelian-groups
open import analysis.cauchy-pseudocompletions-metric-abelian-groups
open import analysis.metric-abelian-groups

open import elementary-number-theory.positive-rational-numbers

open import foundation.binary-relations
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.sets
open import foundation.universe-levels

open import metric-spaces.cauchy-pseudocompletions-of-metric-spaces
open import metric-spaces.isometries-metric-spaces
open import metric-spaces.isometries-pseudometric-spaces
open import metric-spaces.metric-quotients-of-pseudometric-spaces
open import metric-spaces.metric-spaces
open import metric-spaces.pseudometric-spaces
open import metric-spaces.rational-neighborhood-relations
open import metric-spaces.unit-map-metric-quotients-of-pseudometric-spaces
```

</details>

## Idea

The [metric quotient](metric-spaces.metric-quotients-of-pseudometric-spaces.md)
of the
[Cauchy pseudocompletion](analysis.cauchy-pseudocompletions-metric-abelian-groups.md)
of a [metric abelian group](analysis.metric-abelian-groups.md) forms a
[metric space](metric-spaces.metric-spaces.md).

## Definition

```agda
module _
  {l1 l2 : Level}
  (G : Metric-Ab l1 l2)
  where

  metric-quotient-cauchy-pseudocompletion-Metric-Ab :
    Metric-Space (l1 ⊔ l2) (l1 ⊔ l2)
  metric-quotient-cauchy-pseudocompletion-Metric-Ab =
    metric-quotient-Pseudometric-Space (cauchy-pseudocompletion-Metric-Ab G)

  pseudometric-quotient-cauchy-pseudocompletion-Metric-Ab :
    Pseudometric-Space (l1 ⊔ l2) (l1 ⊔ l2)
  pseudometric-quotient-cauchy-pseudocompletion-Metric-Ab =
    pseudometric-Metric-Space metric-quotient-cauchy-pseudocompletion-Metric-Ab

  set-metric-quotient-cauchy-pseudocompletion-Metric-Ab : Set (l1 ⊔ l2)
  set-metric-quotient-cauchy-pseudocompletion-Metric-Ab =
    set-Metric-Space metric-quotient-cauchy-pseudocompletion-Metric-Ab

  type-metric-quotient-cauchy-pseudocompletion-Metric-Ab : UU (l1 ⊔ l2)
  type-metric-quotient-cauchy-pseudocompletion-Metric-Ab =
    type-Set set-metric-quotient-cauchy-pseudocompletion-Metric-Ab

  neighborhood-prop-metric-quotient-cauchy-pseudocompletion-Metric-Ab :
    Rational-Neighborhood-Relation
      ( l1 ⊔ l2)
      ( type-metric-quotient-cauchy-pseudocompletion-Metric-Ab)
  neighborhood-prop-metric-quotient-cauchy-pseudocompletion-Metric-Ab =
    neighborhood-prop-Metric-Space
      ( metric-quotient-cauchy-pseudocompletion-Metric-Ab)

  neighborhood-metric-quotient-cauchy-pseudocompletion-Metric-Ab :
    ℚ⁺ →
    Relation (l1 ⊔ l2) type-metric-quotient-cauchy-pseudocompletion-Metric-Ab
  neighborhood-metric-quotient-cauchy-pseudocompletion-Metric-Ab =
    neighborhood-Metric-Space
      ( metric-quotient-cauchy-pseudocompletion-Metric-Ab)
```

## Properties

### The embedding of elements of a metric abelian group in the metric quotient of its Cauchy pseudocompletion

```agda
module _
  {l1 l2 : Level}
  (G : Metric-Ab l1 l2)
  where

  isometry-in-approximation-metric-quotient-cauchy-pseudocompletion-Metric-Ab :
    isometry-Pseudometric-Space
      ( cauchy-pseudocompletion-Metric-Ab G)
      ( pseudometric-quotient-cauchy-pseudocompletion-Metric-Ab G)
  isometry-in-approximation-metric-quotient-cauchy-pseudocompletion-Metric-Ab =
    isometry-unit-metric-quotient-Pseudometric-Space
      ( cauchy-pseudocompletion-Metric-Ab G)

  isometry-in-metric-quotient-cauchy-pseudocompletion-Metric-Ab :
    isometry-Metric-Space
      ( metric-space-Metric-Ab G)
      ( metric-quotient-cauchy-pseudocompletion-Metric-Ab G)
  isometry-in-metric-quotient-cauchy-pseudocompletion-Metric-Ab =
    comp-isometry-Pseudometric-Space
      ( pseudometric-space-Metric-Ab G)
      ( cauchy-pseudocompletion-Metric-Ab G)
      ( pseudometric-quotient-cauchy-pseudocompletion-Metric-Ab G)
      ( isometry-in-approximation-metric-quotient-cauchy-pseudocompletion-Metric-Ab)
      ( isometry-unit-cauchy-pseudocompletion-Metric-Space
        ( metric-space-Metric-Ab G))

  in-approximation-metric-quotient-cauchy-pseudocompletion-Metric-Ab :
    cauchy-approximation-Metric-Ab G →
    type-metric-quotient-cauchy-pseudocompletion-Metric-Ab G
  in-approximation-metric-quotient-cauchy-pseudocompletion-Metric-Ab =
    map-unit-metric-quotient-Pseudometric-Space
      ( cauchy-pseudocompletion-Metric-Ab G)

  in-metric-quotient-cauchy-pseudocompletion-Metric-Ab :
    type-Metric-Ab G → type-metric-quotient-cauchy-pseudocompletion-Metric-Ab G
  in-metric-quotient-cauchy-pseudocompletion-Metric-Ab x =
    in-approximation-metric-quotient-cauchy-pseudocompletion-Metric-Ab
      ( const-cauchy-approximation-Metric-Ab G x)

  abstract
    is-emb-in-metric-quotient-cauchy-pseudocompletion-Metric-Ab :
      is-emb in-metric-quotient-cauchy-pseudocompletion-Metric-Ab
    is-emb-in-metric-quotient-cauchy-pseudocompletion-Metric-Ab =
      is-emb-map-isometry-Metric-Space
        ( metric-space-Metric-Ab G)
        ( metric-quotient-cauchy-pseudocompletion-Metric-Ab G)
        ( isometry-in-metric-quotient-cauchy-pseudocompletion-Metric-Ab)

  emb-metric-quotient-cauchy-pseudocompletion-Metric-Ab :
    type-Metric-Ab G ↪ type-metric-quotient-cauchy-pseudocompletion-Metric-Ab G
  emb-metric-quotient-cauchy-pseudocompletion-Metric-Ab =
    ( in-metric-quotient-cauchy-pseudocompletion-Metric-Ab ,
      is-emb-in-metric-quotient-cauchy-pseudocompletion-Metric-Ab)

  zero-metric-quotient-cauchy-pseudocompletion-Metric-Ab :
    type-metric-quotient-cauchy-pseudocompletion-Metric-Ab G
  zero-metric-quotient-cauchy-pseudocompletion-Metric-Ab =
    in-metric-quotient-cauchy-pseudocompletion-Metric-Ab (zero-Metric-Ab G)
```
