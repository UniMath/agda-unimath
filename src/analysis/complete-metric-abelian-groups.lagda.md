# Complete metric abelian groups

```agda
module analysis.complete-metric-abelian-groups where
```

<details><summary>Imports</summary>

```agda
open import analysis.metric-abelian-groups

open import foundation.dependent-pair-types
open import foundation.propositions
open import foundation.subtypes
open import foundation.universe-levels

open import metric-spaces.complete-metric-spaces
open import metric-spaces.metric-spaces
```

</details>

## Idea

A {{#concept "complete metric abelian group" Agda=Complete-Metric-Ab}} is a
[metric abelian group](analysis.metric-abelian-groups.md) whose associated
[metric space](metric-spaces.metric-spaces.md) is
[complete](metric-spaces.complete-metric-spaces.md).

## Definition

```agda
is-complete-prop-Metric-Ab : {l1 l2 : Level} → Metric-Ab l1 l2 → Prop (l1 ⊔ l2)
is-complete-prop-Metric-Ab G =
  is-complete-prop-Metric-Space (metric-space-Metric-Ab G)

is-complete-Metric-Ab : {l1 l2 : Level} → Metric-Ab l1 l2 → UU (l1 ⊔ l2)
is-complete-Metric-Ab G = is-complete-Metric-Space (metric-space-Metric-Ab G)

Complete-Metric-Ab : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
Complete-Metric-Ab l1 l2 = type-subtype (is-complete-prop-Metric-Ab {l1} {l2})
```

## Properties

```agda
module _
  {l1 l2 : Level}
  (G : Complete-Metric-Ab l1 l2)
  where

  metric-ab-Complete-Metric-Ab : Metric-Ab l1 l2
  metric-ab-Complete-Metric-Ab = pr1 G

  metric-space-Complete-Metric-Ab : Metric-Space l1 l2
  metric-space-Complete-Metric-Ab =
    metric-space-Metric-Ab metric-ab-Complete-Metric-Ab

  complete-metric-space-Complete-Metric-Ab : Complete-Metric-Space l1 l2
  complete-metric-space-Complete-Metric-Ab =
    ( metric-space-Complete-Metric-Ab , pr2 G)

  type-Complete-Metric-Ab : UU l1
  type-Complete-Metric-Ab = type-Metric-Ab metric-ab-Complete-Metric-Ab
```
