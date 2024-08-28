# Metric structures

```agda
module metric-spaces.metric-structures where
```

<details><summary>Imports</summary>

```agda
open import foundation.propositions
open import foundation.universe-levels

open import metric-spaces.premetric-structures
```

</details>

## Idea

A [premetric structure](metric-spaces.metric-structures.md) is a
{{#concept "metric" Disambiguation="premetric structure" Agda=is-metric-Premetric}}
if it is reflexive, symmetric, local, and triangular.

## Definitions

### The property of being a metric premetric structure

```agda
module _
  {l1 l2 : Level} {A : UU l1} (B : Premetric l2 A)
  where

  is-metric-prop-Premetric : Prop (l1 ⊔ l2)
  is-metric-prop-Premetric =
    product-Prop
      ( is-reflexive-prop-Premetric B)
      ( product-Prop
        ( is-symmetric-prop-Premetric B)
        ( product-Prop
          ( is-local-prop-Premetric B)
          ( is-triangular-prop-Premetric B)))

  is-metric-Premetric : UU (l1 ⊔ l2)
  is-metric-Premetric = type-Prop is-metric-prop-Premetric

  is-prop-is-metric-Premetric : is-prop is-metric-Premetric
  is-prop-is-metric-Premetric =
    is-prop-type-Prop is-metric-prop-Premetric
```
