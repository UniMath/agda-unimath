# Total metric spaces

```agda
module metric-spaces.total-metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.inhabited-subtypes
open import foundation.propositions
open import foundation.subtypes
open import foundation.universe-levels

open import metric-spaces.metric-spaces
```

</details>

## Idea

A [metric space](metric-spaces.metric-spaces.md) is
{{#concept "total" Disambiguation="metric space" Agda=is-total-Metric-Space Agda=Total-Metric-Space}} if
all elements are at bounded distance.

## Definitions

### The property of being a total metric space

```agda
module _
  {l1 l2 : Level} (A : Metric-Space l1 l2)
  where

  is-total-prop-Metric-Space : Prop (l1 ⊔ l2)
  is-total-prop-Metric-Space =
    Π-Prop
      ( type-Metric-Space A)
      ( λ x →
        Π-Prop
          ( type-Metric-Space A)
          ( λ y →
            is-inhabited-subtype-Prop
              ( λ d → structure-Metric-Space A d x y)))

  is-total-Metric-Space : UU (l1 ⊔ l2)
  is-total-Metric-Space =
    type-Prop is-total-prop-Metric-Space
```

### The type of total metric spaces

```agda
module _
  (l1 l2 : Level)
  where

  Total-Metric-Space : UU (lsuc l1 ⊔ lsuc l2)
  Total-Metric-Space =
    type-subtype (is-total-prop-Metric-Space {l1} {l2})

module _
  {l1 l2 : Level} (M : Total-Metric-Space l1 l2)
  where

  metric-space-Total-Metric-Space : Metric-Space l1 l2
  metric-space-Total-Metric-Space = pr1 M

  is-total-metric-space-Total-Metric-Space :
    is-total-Metric-Space metric-space-Total-Metric-Space
  is-total-metric-space-Total-Metric-Space = pr2 M

  type-Total-Metric-Space : UU l1
  type-Total-Metric-Space = type-Metric-Space metric-space-Total-Metric-Space
```
