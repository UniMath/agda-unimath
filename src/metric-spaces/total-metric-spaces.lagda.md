# Total metric spaces

```agda
module metric-spaces.total-metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import foundation.inhabited-subtypes
open import foundation.propositions
open import foundation.universe-levels

open import metric-spaces.metric-spaces
```

</details>

## Idea

A [metric space](metric-spaces.metric-spaces.md) is
{{#concept "total" Disambiguation="metric space" Agda=is-total-Metric-Space}} if
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
