# Cauchy approximations in metric abelian groups

```agda
module analysis.cauchy-approximations-metric-abelian-groups where
```

<details><summary>Imports</summary>

```agda
open import analysis.metric-abelian-groups

open import elementary-number-theory.positive-rational-numbers

open import foundation.subtypes
open import foundation.universe-levels

open import metric-spaces.cauchy-approximations-metric-spaces
```

</details>

## Idea

A
{{#concept "Cauchy approximation" Disambiguation="in a metric abelian group" Agda=cauchy-approximation-Metric-Ab}}
in a [metric abelian group](analysis.metric-abelian-groups.md) is a
[Cauchy approximation](metric-spaces.cauchy-approximations-metric-spaces.md) in
the underlying [metric space](metric-spaces.metric-spaces.md).

## Definition

```agda
module _
  {l1 l2 : Level}
  (G : Metric-Ab l1 l2)
  where

  is-cauchy-approximation-prop-Metric-Ab : subtype l2 (ℚ⁺ → type-Metric-Ab G)
  is-cauchy-approximation-prop-Metric-Ab =
    is-cauchy-approximation-prop-Metric-Space (metric-space-Metric-Ab G)

  is-cauchy-approximation-Metric-Ab : (ℚ⁺ → type-Metric-Ab G) → UU l2
  is-cauchy-approximation-Metric-Ab =
    is-in-subtype is-cauchy-approximation-prop-Metric-Ab

  cauchy-approximation-Metric-Ab : UU (l1 ⊔ l2)
  cauchy-approximation-Metric-Ab =
    type-subtype is-cauchy-approximation-prop-Metric-Ab
```

## Properties

### Constant maps in metric abelian groups are Cauchy approximations

```agda
module _
  {l1 l2 : Level}
  (G : Metric-Ab l1 l2)
  where

  const-cauchy-approximation-Metric-Ab :
    type-Metric-Ab G → cauchy-approximation-Metric-Ab G
  const-cauchy-approximation-Metric-Ab =
    const-cauchy-approximation-Metric-Space (metric-space-Metric-Ab G)

  zero-cauchy-approximation-Metric-Ab :
    cauchy-approximation-Metric-Ab G
  zero-cauchy-approximation-Metric-Ab =
    const-cauchy-approximation-Metric-Ab (zero-Metric-Ab G)
```
