# Cocones over sequential diagrams of isometries between metric spaces

```agda
module metric-spaces.cocones-sequential-diagrams-isometries-metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.dependent-products-propositions
open import foundation.function-types
open import foundation.homotopies
open import foundation.propositions
open import foundation.subtypes
open import foundation.universe-levels

open import metric-spaces.isometries-metric-spaces
open import metric-spaces.metric-spaces
open import metric-spaces.sequential-diagrams-isometries-metric-spaces
```

</details>

## Idea

A
{{#concept "cocone" Disambiguation="under a sequential diagram of isometries Agda=cocone-sequential-diagram-isometry-Metric-Space}}
under a
[sequential diagram](metric-spaces.sequential-diagrams-isometries-metric-spaces.md)
of [isometries](metric-spaces.isometries-metric-spaces.md) between
[metric spaces](metric-spaces.metric-spaces.md)

```text
     f₀       f₁       f₂
 M₀ ----> M₁ ----> M₂ ----> ⋯
```

with codomain a metric space `X : Metric-Space` consists of a family of
isometries `iₙ : Mₙ → X` such that the following triangles:

```text
       fₙ
 Mₙ ------> Mₙ₊₁
   \       /
    \     /
  iₙ \   / iₙ₊₁
      ∨ ∨
       X
```

[commute](foundation.commuting-triangles-of-maps.md).

## Definitions

### Cocones under sequential diagrams of isometries

```agda
module _
  { l1 l2 l3 l4 : Level}
  ( M : sequential-diagram-isometry-Metric-Space l1 l2)
  ( X : Metric-Space l3 l4)
  ( f :
    (n : ℕ) →
    isometry-Metric-Space
      ( seq-metric-space-sequential-diagram-isometry-Metric-Space M n)
      ( X))
  where

  is-coherent-seq-map-prop-cocone-sequential-diagram-isometry-Metric-Space :
    Prop (l1 ⊔ l3)
  is-coherent-seq-map-prop-cocone-sequential-diagram-isometry-Metric-Space =
    Π-Prop
      ( ℕ)
      ( λ n →
        htpy-map-prop-isometry-Metric-Space
          ( seq-metric-space-sequential-diagram-isometry-Metric-Space M n)
          ( X)
          ( f n)
          ( comp-isometry-Metric-Space
            ( seq-metric-space-sequential-diagram-isometry-Metric-Space M n)
            ( seq-metric-space-sequential-diagram-isometry-Metric-Space
              ( M)
              ( succ-ℕ n))
            ( X)
            ( f (succ-ℕ n))
            ( seq-isometry-sequential-diagram-isometry-Metric-Space M n)))

  is-coherent-seq-map-cocone-sequential-diagram-isometry-Metric-Space :
    UU (l1 ⊔ l3)
  is-coherent-seq-map-cocone-sequential-diagram-isometry-Metric-Space =
    type-Prop
      is-coherent-seq-map-prop-cocone-sequential-diagram-isometry-Metric-Space

  is-prop-is-coherent-seq-map-cocone-sequential-diagram-isometry-Metric-Space :
    is-prop
      is-coherent-seq-map-cocone-sequential-diagram-isometry-Metric-Space
  is-prop-is-coherent-seq-map-cocone-sequential-diagram-isometry-Metric-Space =
    is-prop-type-Prop
      is-coherent-seq-map-prop-cocone-sequential-diagram-isometry-Metric-Space

module _
  {l1 l2 l3 l4 : Level}
  (M : sequential-diagram-isometry-Metric-Space l1 l2)
  (X : Metric-Space l3 l4)
  where

  cocone-sequential-diagram-isometry-Metric-Space : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  cocone-sequential-diagram-isometry-Metric-Space =
    type-subtype
      ( is-coherent-seq-map-prop-cocone-sequential-diagram-isometry-Metric-Space
        ( M)
        ( X))

module _
  {l1 l2 l3 l4 : Level}
  (M : sequential-diagram-isometry-Metric-Space l1 l2)
  (X : Metric-Space l3 l4)
  (C : cocone-sequential-diagram-isometry-Metric-Space M X)
  where

  seq-isometry-cocone-sequential-diagram-isometry-Metric-Space :
    (n : ℕ) →
    isometry-Metric-Space
      ( seq-metric-space-sequential-diagram-isometry-Metric-Space M n)
      ( X)
  seq-isometry-cocone-sequential-diagram-isometry-Metric-Space = pr1 C

  seq-map-isometry-cocone-sequential-diagram-isometry-Metric-Space :
    (n : ℕ) →
    family-sequential-diagram-isometry-Metric-Space M n →
    type-Metric-Space X
  seq-map-isometry-cocone-sequential-diagram-isometry-Metric-Space n =
    map-isometry-Metric-Space
      ( seq-metric-space-sequential-diagram-isometry-Metric-Space M n)
      ( X)
      ( seq-isometry-cocone-sequential-diagram-isometry-Metric-Space n)

  coh-triangle-cocone-sequential-diagram-isometry-Metric-Space :
    is-coherent-seq-map-cocone-sequential-diagram-isometry-Metric-Space
      ( M)
      ( X)
      ( seq-isometry-cocone-sequential-diagram-isometry-Metric-Space)
  coh-triangle-cocone-sequential-diagram-isometry-Metric-Space = pr2 C
```
