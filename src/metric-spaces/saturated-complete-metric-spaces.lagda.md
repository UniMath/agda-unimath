# Saturated complete metric spaces

```agda
module metric-spaces.saturated-complete-metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.propositions
open import foundation.subtypes
open import foundation.universe-levels

open import metric-spaces.cauchy-approximations-metric-spaces
open import metric-spaces.complete-metric-spaces
open import metric-spaces.convergent-cauchy-approximations-metric-spaces
open import metric-spaces.metric-spaces
open import metric-spaces.saturated-metric-spaces
```

</details>

## Idea

A [metric space](metric-spaces.metric-spaces.md) is
{{#concept "saturated and complete" Disambiguation="metric space" Agda=Saturated-Complete-Metric-Space}},
or **saturated complete**, if it is
[complete](metric-spaces.complete-metric-spaces.md) and
[saturated](metric-spaces.saturated-metric-spaces.md).

## Definitions

### The property of being a saturated complete metric space

```agda
module _
  {l1 l2 : Level} (A : Metric-Space l1 l2)
  where

  is-saturated-complete-prop-Metric-Space : Prop (l1 ⊔ l2)
  is-saturated-complete-prop-Metric-Space =
    product-Prop
      ( is-complete-prop-Metric-Space A)
      ( is-saturated-prop-Metric-Space A)

  is-saturated-complete-Metric-Space : UU (l1 ⊔ l2)
  is-saturated-complete-Metric-Space =
    type-Prop is-saturated-complete-prop-Metric-Space

  is-prop-is-saturated-complete-Metric-Space : is-prop
    is-saturated-complete-Metric-Space
  is-prop-is-saturated-complete-Metric-Space =
    is-prop-type-Prop is-saturated-complete-prop-Metric-Space
```

### The type of saturated complete metric spaces

```agda
module _
  (l1 l2 : Level)
  where

  Saturated-Complete-Metric-Space : UU (lsuc l1 ⊔ lsuc l2)
  Saturated-Complete-Metric-Space =
    type-subtype (is-saturated-complete-prop-Metric-Space {l1} {l2})
```

```agda
module _
  {l1 l2 : Level}
  (A : Saturated-Complete-Metric-Space l1 l2)
  where

  metric-space-Saturated-Complete-Metric-Space : Metric-Space l1 l2
  metric-space-Saturated-Complete-Metric-Space = pr1 A

  type-Saturated-Complete-Metric-Space : UU l1
  type-Saturated-Complete-Metric-Space =
    type-Metric-Space metric-space-Saturated-Complete-Metric-Space

  is-complete-metric-space-Saturated-Complete-Metric-Space :
    is-complete-Metric-Space metric-space-Saturated-Complete-Metric-Space
  is-complete-metric-space-Saturated-Complete-Metric-Space = pr1 (pr2 A)

  complete-metric-space-Saturated-Complete-Metric-Space :
    Complete-Metric-Space l1 l2
  complete-metric-space-Saturated-Complete-Metric-Space =
    metric-space-Saturated-Complete-Metric-Space ,
    is-complete-metric-space-Saturated-Complete-Metric-Space

  is-saturated-metric-space-Saturated-Complete-Metric-Space :
    is-saturated-Metric-Space metric-space-Saturated-Complete-Metric-Space
  is-saturated-metric-space-Saturated-Complete-Metric-Space = pr2 (pr2 A)
```

### The map from Cauchy approximations in a saturated complete metric space to convergent Cauchy approximations

```agda
module _
  {l1 l2 : Level}
  (A : Saturated-Complete-Metric-Space l1 l2)
  where

  convergent-cauchy-approximation-Saturated-Complete-Metric-Space :
    cauchy-approximation-Metric-Space
      ( metric-space-Saturated-Complete-Metric-Space A) →
    convergent-cauchy-approximation-Metric-Space
      ( metric-space-Saturated-Complete-Metric-Space A)
  convergent-cauchy-approximation-Saturated-Complete-Metric-Space u =
    u , is-complete-metric-space-Saturated-Complete-Metric-Space A u
```

### The limit of a Cauchy approximation in a saturated complete metric space

```agda
module _
  {l1 l2 : Level}
  (A : Saturated-Complete-Metric-Space l1 l2)
  where

  limit-cauchy-approximation-Saturated-Complete-Metric-Space :
    cauchy-approximation-Metric-Space
      ( metric-space-Saturated-Complete-Metric-Space A) →
    type-Saturated-Complete-Metric-Space A
  limit-cauchy-approximation-Saturated-Complete-Metric-Space u =
    limit-convergent-cauchy-approximation-Metric-Space
      ( metric-space-Saturated-Complete-Metric-Space A)
      ( convergent-cauchy-approximation-Saturated-Complete-Metric-Space A u)
```
