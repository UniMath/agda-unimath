# Complete metric spaces

```agda
module metric-spaces.complete-metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.positive-rational-numbers

open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.identity-types
open import foundation.propositions
open import foundation.retractions
open import foundation.sections
open import foundation.subtypes
open import foundation.universe-levels

open import metric-spaces.cauchy-approximations-metric-spaces
open import metric-spaces.convergent-cauchy-approximations-metric-spaces
open import metric-spaces.metric-spaces
```

</details>

## Idea

A [metric space](metric-spaces.metric-spaces.md) is
{{#concept "complete" Disambiguation="metric space" Agda=is-complete-Metric-Space WD="complete metric space" WDID=Q848569}}
if all its
[Cauchy approximations](metric-spaces.cauchy-approximations-metric-spaces.md)
are
[convergent](metric-spaces.convergent-cauchy-approximations-metric-spaces.md).

## Definitions

### The property of being a complete metric space

```agda
module _
  {l1 l2 : Level} (A : Metric-Space l1 l2)
  where

  is-complete-prop-Metric-Space : Prop (l1 ⊔ l2)
  is-complete-prop-Metric-Space =
    Π-Prop
      ( cauchy-approximation-Metric-Space A)
      ( is-convergent-prop-cauchy-approximation-Metric-Space A)

  is-complete-Metric-Space : UU (l1 ⊔ l2)
  is-complete-Metric-Space = type-Prop is-complete-prop-Metric-Space

  is-prop-is-complete-Metric-Space : is-prop is-complete-Metric-Space
  is-prop-is-complete-Metric-Space =
    is-prop-type-Prop is-complete-prop-Metric-Space
```

### The type of complete metric spaces

```agda
module _
  (l1 l2 : Level)
  where

  Complete-Metric-Space : UU (lsuc l1 ⊔ lsuc l2)
  Complete-Metric-Space =
    type-subtype (is-complete-prop-Metric-Space {l1} {l2})
```

```agda
module _
  {l1 l2 : Level}
  (A : Complete-Metric-Space l1 l2)
  where

  metric-space-Complete-Metric-Space : Metric-Space l1 l2
  metric-space-Complete-Metric-Space = pr1 A

  type-Complete-Metric-Space : UU l1
  type-Complete-Metric-Space =
    type-Metric-Space metric-space-Complete-Metric-Space

  is-complete-metric-space-Complete-Metric-Space :
    is-complete-Metric-Space metric-space-Complete-Metric-Space
  is-complete-metric-space-Complete-Metric-Space = pr2 A
```

### The equivalence between Cauchy approximations and convergent Cauchy approximations in a complete metric space

```agda
module _
  {l1 l2 : Level}
  (A : Complete-Metric-Space l1 l2)
  where

  convergent-cauchy-approximation-Complete-Metric-Space :
    cauchy-approximation-Metric-Space
      ( metric-space-Complete-Metric-Space A) →
    convergent-cauchy-approximation-Metric-Space
      ( metric-space-Complete-Metric-Space A)
  convergent-cauchy-approximation-Complete-Metric-Space u =
    ( u , is-complete-metric-space-Complete-Metric-Space A u)

  is-section-convergent-cauchy-approximation-Complete-Metric-Space :
    is-section
      ( convergent-cauchy-approximation-Complete-Metric-Space)
      ( inclusion-subtype
        ( is-convergent-prop-cauchy-approximation-Metric-Space
          ( metric-space-Complete-Metric-Space A)))
  is-section-convergent-cauchy-approximation-Complete-Metric-Space u =
    eq-type-subtype
      ( is-convergent-prop-cauchy-approximation-Metric-Space
        ( metric-space-Complete-Metric-Space A))
      ( refl)

  is-retraction-convergent-cauchy-approximation-Metric-Space :
    is-retraction
      ( convergent-cauchy-approximation-Complete-Metric-Space)
      ( inclusion-subtype
        ( is-convergent-prop-cauchy-approximation-Metric-Space
          ( metric-space-Complete-Metric-Space A)))
  is-retraction-convergent-cauchy-approximation-Metric-Space u = refl

  is-equiv-convergent-cauchy-approximation-Complete-Metric-Space :
    is-equiv convergent-cauchy-approximation-Complete-Metric-Space
  pr1 is-equiv-convergent-cauchy-approximation-Complete-Metric-Space =
    ( inclusion-subtype
      ( is-convergent-prop-cauchy-approximation-Metric-Space
        ( metric-space-Complete-Metric-Space A))) ,
    ( is-section-convergent-cauchy-approximation-Complete-Metric-Space)
  pr2 is-equiv-convergent-cauchy-approximation-Complete-Metric-Space =
    ( inclusion-subtype
      ( is-convergent-prop-cauchy-approximation-Metric-Space
        ( metric-space-Complete-Metric-Space A))) ,
    ( is-retraction-convergent-cauchy-approximation-Metric-Space)
```

### The limit of a Cauchy approximation in a complete metric space

```agda
module _
  { l1 l2 : Level}
  ( A : Complete-Metric-Space l1 l2)
  ( u : cauchy-approximation-Metric-Space
    ( metric-space-Complete-Metric-Space A))
  where

  limit-cauchy-approximation-Complete-Metric-Space :
    type-Complete-Metric-Space A
  limit-cauchy-approximation-Complete-Metric-Space =
    limit-convergent-cauchy-approximation-Metric-Space
      ( metric-space-Complete-Metric-Space A)
      ( convergent-cauchy-approximation-Complete-Metric-Space A u)

  is-limit-limit-cauchy-approximation-Complete-Metric-Space :
    is-limit-cauchy-approximation-Metric-Space
      ( metric-space-Complete-Metric-Space A)
      ( u)
      ( limit-cauchy-approximation-Complete-Metric-Space)
  is-limit-limit-cauchy-approximation-Complete-Metric-Space =
    is-limit-limit-convergent-cauchy-approximation-Metric-Space
      ( metric-space-Complete-Metric-Space A)
      ( convergent-cauchy-approximation-Complete-Metric-Space A u)
```

## External links

- [Complete metric space](https://en.wikipedia.org/wiki/Complete_metric_space)
  at Wikipedia
