# Complete metric spaces (WIP)

```agda
module metric-spaces.complete-metric-spaces-WIP where
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

open import metric-spaces.cauchy-approximations-metric-spaces-WIP
open import metric-spaces.convergent-cauchy-approximations-metric-spaces-WIP
open import metric-spaces.limits-of-cauchy-approximations-metric-spaces-WIP
open import metric-spaces.metric-spaces-WIP
```

</details>

## Idea

A [metric space](metric-spaces.metric-spaces-WIP.md) is
{{#concept "complete" Disambiguation="metric space" Agda=is-complete-Metric-Space-WIP WD="complete metric space" WDID=Q848569}}
if all its
[Cauchy approximations](metric-spaces.cauchy-approximations-metric-spaces-WIP.md)
are
[convergent](metric-spaces.convergent-cauchy-approximations-metric-spaces-WIP.md).

## Definitions

### The property of being a complete metric space

```agda
module _
  {l1 l2 : Level} (A : Metric-Space-WIP l1 l2)
  where

  is-complete-prop-Metric-Space-WIP : Prop (l1 ⊔ l2)
  is-complete-prop-Metric-Space-WIP =
    Π-Prop
      ( cauchy-approximation-Metric-Space-WIP A)
      ( is-convergent-prop-cauchy-approximation-Metric-Space-WIP A)

  is-complete-Metric-Space-WIP : UU (l1 ⊔ l2)
  is-complete-Metric-Space-WIP = type-Prop is-complete-prop-Metric-Space-WIP

  is-prop-is-complete-Metric-Space-WIP : is-prop is-complete-Metric-Space-WIP
  is-prop-is-complete-Metric-Space-WIP =
    is-prop-type-Prop is-complete-prop-Metric-Space-WIP
```

### The type of complete metric spaces

```agda
module _
  (l1 l2 : Level)
  where

  Complete-Metric-Space-WIP : UU (lsuc l1 ⊔ lsuc l2)
  Complete-Metric-Space-WIP =
    type-subtype (is-complete-prop-Metric-Space-WIP {l1} {l2})
```

```agda
module _
  {l1 l2 : Level}
  (A : Complete-Metric-Space-WIP l1 l2)
  where

  metric-space-Complete-Metric-Space-WIP : Metric-Space-WIP l1 l2
  metric-space-Complete-Metric-Space-WIP = pr1 A

  type-Complete-Metric-Space-WIP : UU l1
  type-Complete-Metric-Space-WIP =
    type-Metric-Space-WIP metric-space-Complete-Metric-Space-WIP

  is-complete-metric-space-Complete-Metric-Space-WIP :
    is-complete-Metric-Space-WIP metric-space-Complete-Metric-Space-WIP
  is-complete-metric-space-Complete-Metric-Space-WIP = pr2 A
```

### The equivalence between Cauchy approximations and convergent Cauchy approximations in a complete metric space

```agda
module _
  {l1 l2 : Level}
  (A : Complete-Metric-Space-WIP l1 l2)
  where

  convergent-cauchy-approximation-Complete-Metric-Space-WIP :
    cauchy-approximation-Metric-Space-WIP
      ( metric-space-Complete-Metric-Space-WIP A) →
    convergent-cauchy-approximation-Metric-Space-WIP
      ( metric-space-Complete-Metric-Space-WIP A)
  convergent-cauchy-approximation-Complete-Metric-Space-WIP u =
    ( u , is-complete-metric-space-Complete-Metric-Space-WIP A u)

  is-section-convergent-cauchy-approximation-Complete-Metric-Space-WIP :
    is-section
      ( convergent-cauchy-approximation-Complete-Metric-Space-WIP)
      ( inclusion-subtype
        ( is-convergent-prop-cauchy-approximation-Metric-Space-WIP
          ( metric-space-Complete-Metric-Space-WIP A)))
  is-section-convergent-cauchy-approximation-Complete-Metric-Space-WIP u =
    eq-type-subtype
      ( is-convergent-prop-cauchy-approximation-Metric-Space-WIP
        ( metric-space-Complete-Metric-Space-WIP A))
      ( refl)

  is-retraction-convergent-cauchy-approximation-Metric-Space-WIP :
    is-retraction
      ( convergent-cauchy-approximation-Complete-Metric-Space-WIP)
      ( inclusion-subtype
        ( is-convergent-prop-cauchy-approximation-Metric-Space-WIP
          ( metric-space-Complete-Metric-Space-WIP A)))
  is-retraction-convergent-cauchy-approximation-Metric-Space-WIP u = refl

  is-equiv-convergent-cauchy-approximation-Complete-Metric-Space-WIP :
    is-equiv convergent-cauchy-approximation-Complete-Metric-Space-WIP
  pr1 is-equiv-convergent-cauchy-approximation-Complete-Metric-Space-WIP =
    ( inclusion-subtype
      ( is-convergent-prop-cauchy-approximation-Metric-Space-WIP
        ( metric-space-Complete-Metric-Space-WIP A))) ,
    ( is-section-convergent-cauchy-approximation-Complete-Metric-Space-WIP)
  pr2 is-equiv-convergent-cauchy-approximation-Complete-Metric-Space-WIP =
    ( inclusion-subtype
      ( is-convergent-prop-cauchy-approximation-Metric-Space-WIP
        ( metric-space-Complete-Metric-Space-WIP A))) ,
    ( is-retraction-convergent-cauchy-approximation-Metric-Space-WIP)
```

### The limit of a Cauchy approximation in a complete metric space

```agda
module _
  { l1 l2 : Level}
  ( A : Complete-Metric-Space-WIP l1 l2)
  ( u : cauchy-approximation-Metric-Space-WIP
    ( metric-space-Complete-Metric-Space-WIP A))
  where

  limit-cauchy-approximation-Complete-Metric-Space-WIP :
    type-Complete-Metric-Space-WIP A
  limit-cauchy-approximation-Complete-Metric-Space-WIP =
    limit-convergent-cauchy-approximation-Metric-Space-WIP
      ( metric-space-Complete-Metric-Space-WIP A)
      ( convergent-cauchy-approximation-Complete-Metric-Space-WIP A u)

  is-limit-limit-cauchy-approximation-Complete-Metric-Space-WIP :
    is-limit-cauchy-approximation-Metric-Space-WIP
      ( metric-space-Complete-Metric-Space-WIP A)
      ( u)
      ( limit-cauchy-approximation-Complete-Metric-Space-WIP)
  is-limit-limit-cauchy-approximation-Complete-Metric-Space-WIP =
    is-limit-limit-convergent-cauchy-approximation-Metric-Space-WIP
      ( metric-space-Complete-Metric-Space-WIP A)
      ( convergent-cauchy-approximation-Complete-Metric-Space-WIP A u)
```

## External links

- [Complete metric space](https://en.wikipedia.org/wiki/Complete_metric_space)
  at Wikipedia
