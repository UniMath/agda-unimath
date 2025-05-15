# Total metric spaces

```agda
module metric-spaces.total-metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.disjunction
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.functoriality-propositional-truncation
open import foundation.inhabited-subtypes
open import foundation.propositions
open import foundation.subtypes
open import foundation.universe-levels

open import metric-spaces.elements-at-bounded-distance-metric-spaces
open import metric-spaces.metric-spaces

open import order-theory.total-preorders
```

</details>

## Idea

A [metric space](metric-spaces.metric-spaces.md) is
{{#concept "total" Disambiguation="metric space" Agda=is-total-Metric-Space Agda=Total-Metric-Space}}
if all elements are at bounded distance, i.e., if the
[preorder of elements at bounded distance in the metric space](metric-spaces.elements-at-bounded-distance-metric-spacesa.md)
is [total](order-theory.total-preorders.md).

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

## Properties

neigbor

### A metric space is total if and only if the preorder of elements at bounded distance is total

```agda
module _
  {l1 l2 : Level} (A : Metric-Space l1 l2)
  where

  is-total-preorder-is-element-at-bounded-dist-is-total-Metric-Space :
    is-total-Metric-Space A →
    is-total-Preorder
      (preorder-is-element-at-bounded-dist-Metric-Space A)
  is-total-preorder-is-element-at-bounded-dist-is-total-Metric-Space
    total-A x y =
    inl-disjunction (total-A x y)

  is-total-is-total-preorder-is-element-at-bounded-dist-Metric-Space :
    is-total-Preorder
      (preorder-is-element-at-bounded-dist-Metric-Space A) →
    is-total-Metric-Space A
  is-total-is-total-preorder-is-element-at-bounded-dist-Metric-Space
    total-N x y =
    elim-disjunction
      ( is-element-at-bounded-dist-prop-Metric-Space A x y)
      ( id)
      ( map-trunc-Prop (tot λ d → is-symmetric-structure-Metric-Space A d y x))
      ( total-N x y)
```
