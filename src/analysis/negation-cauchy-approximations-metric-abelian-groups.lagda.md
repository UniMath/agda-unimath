# Negation of Cauchy approximations in metric abelian groups

```agda
module analysis.negation-cauchy-approximations-metric-abelian-groups where
```

<details><summary>Imports</summary>

```agda
open import analysis.addition-cauchy-approximations-metric-abelian-groups
open import analysis.cauchy-approximations-metric-abelian-groups
open import analysis.cauchy-pseudocompletions-metric-abelian-groups
open import analysis.metric-abelian-groups

open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.identity-types
open import foundation.subtypes
open import foundation.universe-levels

open import metric-spaces.functoriality-isometries-cauchy-pseudocompletions-of-metric-spaces
open import metric-spaces.isometries-pseudometric-spaces
```

</details>

## Idea

Negation of
[Cauchy approximations](analysis.cauchy-approximations-metric-abelian-groups.md)
in [metric abelian groups](analysis.metric-abelian-groups.md) is the inverse
operation for
[addition](analysis.addition-cauchy-approximations-metric-abelian-groups.md).

## Definition

```agda
module _
  {l1 l2 : Level}
  (G : Metric-Ab l1 l2)
  where

  neg-cauchy-approximation-Metric-Ab :
    cauchy-approximation-Metric-Ab G → cauchy-approximation-Metric-Ab G
  neg-cauchy-approximation-Metric-Ab =
    map-isometry-cauchy-pseudocompletion-Metric-Space
      ( metric-space-Metric-Ab G)
      ( metric-space-Metric-Ab G)
      ( isometry-neg-Metric-Ab G)
```

## Properties

### Negation is an isometry in the Cauchy pseudocompletion of metric abelian groups

```agda
module _
  {l1 l2 : Level}
  (G : Metric-Ab l1 l2)
  where

  isometry-neg-cauchy-pseudocompletion-Metric-Ab :
    isometry-Pseudometric-Space
      ( cauchy-pseudocompletion-Metric-Ab G)
      ( cauchy-pseudocompletion-Metric-Ab G)
  isometry-neg-cauchy-pseudocompletion-Metric-Ab =
    isometry-cauchy-pseudocompletion-Metric-Space
      ( metric-space-Metric-Ab G)
      ( metric-space-Metric-Ab G)
      ( isometry-neg-Metric-Ab G)

  abstract
    is-isometry-neg-cauchy-pseudocompletion-Metric-Ab :
      is-isometry-Pseudometric-Space
        ( cauchy-pseudocompletion-Metric-Ab G)
        ( cauchy-pseudocompletion-Metric-Ab G)
        ( neg-cauchy-approximation-Metric-Ab G)
    is-isometry-neg-cauchy-pseudocompletion-Metric-Ab =
      is-isometry-map-isometry-Pseudometric-Space
        ( cauchy-pseudocompletion-Metric-Ab G)
        ( cauchy-pseudocompletion-Metric-Ab G)
        ( isometry-neg-cauchy-pseudocompletion-Metric-Ab)
```

### Inverse laws of addition of Cauchy approximations

```agda
module _
  {l1 l2 : Level}
  (G : Metric-Ab l1 l2)
  (ax@(x , is-approx-x) : cauchy-approximation-Metric-Ab G)
  where abstract opaque

  unfolding map-add-cauchy-approximation-Metric-Ab

  left-inverse-law-add-cauchy-approximation-Metric-Ab :
    add-cauchy-approximation-Metric-Ab G
      ( neg-cauchy-approximation-Metric-Ab G ax)
      ( ax) ＝
    zero-cauchy-approximation-Metric-Ab G
  left-inverse-law-add-cauchy-approximation-Metric-Ab =
    eq-type-subtype
      ( is-cauchy-approximation-prop-Metric-Ab G)
      ( eq-htpy (λ _ → left-inverse-law-add-Metric-Ab G _))

  right-inverse-law-add-cauchy-approximation-Metric-Ab :
    add-cauchy-approximation-Metric-Ab G
      ( ax)
      ( neg-cauchy-approximation-Metric-Ab G ax) ＝
    zero-cauchy-approximation-Metric-Ab G
  right-inverse-law-add-cauchy-approximation-Metric-Ab =
    eq-type-subtype
      ( is-cauchy-approximation-prop-Metric-Ab G)
      ( eq-htpy (λ _ → right-inverse-law-add-Metric-Ab G _))
```
