# Morphisms of sequential diagrams of isometries between metric spaces

```agda
module metric-spaces.morphisms-sequential-diagrams-isometries-metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.equality-natural-numbers
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.dependent-products-propositions
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.propositions
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import metric-spaces.indexed-sums-metric-spaces
open import metric-spaces.isometries-metric-spaces
open import metric-spaces.metric-spaces
open import metric-spaces.sequential-diagrams-isometries-metric-spaces

open import synthetic-homotopy-theory.morphisms-sequential-diagrams
open import synthetic-homotopy-theory.sequential-diagrams
```

</details>

## Idea

A
{{#concept "morphism" Disambiguation="between sequential diagrams of isometries" Agda=hom-sequential-diagram-isometry-Metric-Space}}
between
[sequential diagrams](metric-spaces.sequential-diagrams-isometries-metric-spaces.md)
of [isometries](metric-spaces.isometries-metric-spaces.md) between
[metric spaces](metric-spaces.metric-spaces.md):

```text
     g₀       g₁       g₂
 X₀ ----> X₁ ----> X₂ ----> ⋯
```

and

```text
     h₀       h₁       h₂
 Y₀ ----> Y₁ ----> Y₂ ----> ⋯
```

is a sequence `f : (n : ℕ) → isometry Xₙ Yₙ` such that all squares

```text
        gₙ
    Xₙ ---> Xₙ₊₁
    |       |
 fₙ |       | fₙ₊₁
    ∨       ∨
    Yₙ ---> Yₙ₊₁
        hₙ
```

[commute](foundation.commuting-squares-of-maps.md), i.e., a sequence of
isometries whose underlying maps forms a
[morphism](synthetic-homotopy-theory.morphisms-sequential-diagrams.md) between
the underlying
[sequential diagrams](synthetic-homotopy-theory.sequential-diagrams.md).

## Definitions

### Natural isometries between sequential diagrams of isometries

```agda
module _
  { l1 l2 l3 l4 : Level}
  ( X : sequential-diagram-isometry-Metric-Space l1 l2)
  ( Y : sequential-diagram-isometry-Metric-Space l3 l4)
  ( f :
    (n : ℕ) →
    isometry-Metric-Space
      ( seq-metric-space-sequential-diagram-isometry-Metric-Space X n)
      ( seq-metric-space-sequential-diagram-isometry-Metric-Space Y n))
  where

  naturality-hom-sequential-diagram-isometry-Metric-Space : UU (l1 ⊔ l3)
  naturality-hom-sequential-diagram-isometry-Metric-Space =
    naturality-hom-sequential-diagram
      ( diagram-sequential-diagram-isometry-Metric-Space X)
      ( diagram-sequential-diagram-isometry-Metric-Space Y)
      ( λ n →
        map-isometry-Metric-Space
          ( seq-metric-space-sequential-diagram-isometry-Metric-Space X n)
          ( seq-metric-space-sequential-diagram-isometry-Metric-Space Y n)
          ( f n))

  is-prop-naturality-hom-sequential-diagram-isometry-Metric-Space :
    is-prop naturality-hom-sequential-diagram-isometry-Metric-Space
  is-prop-naturality-hom-sequential-diagram-isometry-Metric-Space =
    is-prop-Π
      ( λ i →
        is-prop-Π
          ( λ x →
            is-set-type-Metric-Space
              ( seq-metric-space-sequential-diagram-isometry-Metric-Space
                ( Y)
                ( succ-ℕ i))
              ( _)
              ( _)))

  naturality-prop-hom-sequential-diagram-isometry-Metric-Space : Prop (l1 ⊔ l3)
  naturality-prop-hom-sequential-diagram-isometry-Metric-Space =
    ( naturality-hom-sequential-diagram-isometry-Metric-Space ,
      is-prop-naturality-hom-sequential-diagram-isometry-Metric-Space)
```

### Morphisms of sequential diagrams of isometries

```agda
module _
  {l1 l2 l3 l4 : Level}
  (X : sequential-diagram-isometry-Metric-Space l1 l2)
  (Y : sequential-diagram-isometry-Metric-Space l3 l4)
  where

  hom-sequential-diagram-isometry-Metric-Space : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  hom-sequential-diagram-isometry-Metric-Space =
    type-subtype
      ( naturality-prop-hom-sequential-diagram-isometry-Metric-Space X Y)

module _
  {l1 l2 l3 l4 : Level}
  (X : sequential-diagram-isometry-Metric-Space l1 l2)
  (Y : sequential-diagram-isometry-Metric-Space l3 l4)
  (h : hom-sequential-diagram-isometry-Metric-Space X Y)
  where

  seq-isometry-hom-sequential-diagram-isometry-Metric-Space :
    (n : ℕ) →
    isometry-Metric-Space
      ( seq-metric-space-sequential-diagram-isometry-Metric-Space X n)
      ( seq-metric-space-sequential-diagram-isometry-Metric-Space Y n)
  seq-isometry-hom-sequential-diagram-isometry-Metric-Space = pr1 h

  seq-map-isometry-hom-sequential-diagram-isometry-Metric-Space :
    (n : ℕ) →
    family-sequential-diagram-isometry-Metric-Space X n →
    family-sequential-diagram-isometry-Metric-Space Y n
  seq-map-isometry-hom-sequential-diagram-isometry-Metric-Space n =
    map-isometry-Metric-Space
      ( seq-metric-space-sequential-diagram-isometry-Metric-Space X n)
      ( seq-metric-space-sequential-diagram-isometry-Metric-Space Y n)
      ( seq-isometry-hom-sequential-diagram-isometry-Metric-Space n)

  naturality-seq-isometry-hom-sequential-diagram-isometry-Metric-Space :
    naturality-hom-sequential-diagram-isometry-Metric-Space
      ( X)
      ( Y)
      ( seq-isometry-hom-sequential-diagram-isometry-Metric-Space)
  naturality-seq-isometry-hom-sequential-diagram-isometry-Metric-Space = pr2 h

  hom-diagram-hom-sequential-diagram-isometry-Metric-Space :
    hom-sequential-diagram
      ( diagram-sequential-diagram-isometry-Metric-Space X)
      ( diagram-sequential-diagram-isometry-Metric-Space Y)
  hom-diagram-hom-sequential-diagram-isometry-Metric-Space =
    ( seq-map-isometry-hom-sequential-diagram-isometry-Metric-Space ,
      naturality-seq-isometry-hom-sequential-diagram-isometry-Metric-Space)
```

### The identity morphism of sequential diagrams of isometries

```agda
module _
  {l1 l2 : Level}
  (M : sequential-diagram-isometry-Metric-Space l1 l2)
  where

  id-hom-sequential-diagram-isometry-Metric-Space :
    hom-sequential-diagram-isometry-Metric-Space M M
  pr1 id-hom-sequential-diagram-isometry-Metric-Space n =
    id-isometry-Metric-Space
      ( seq-metric-space-sequential-diagram-isometry-Metric-Space M n)
  pr2 id-hom-sequential-diagram-isometry-Metric-Space n =
    refl-htpy
```

### Composition of morphisms of sequential diagrams of isometries

```agda
module _
  {lx lx' ly ly' lz lz' : Level}
  (X : sequential-diagram-isometry-Metric-Space lx lx')
  (Y : sequential-diagram-isometry-Metric-Space ly ly')
  (Z : sequential-diagram-isometry-Metric-Space lz lz')
  (h : hom-sequential-diagram-isometry-Metric-Space Y Z)
  (f : hom-sequential-diagram-isometry-Metric-Space X Y)
  where

  seq-isometry-comp-hom-sequential-diagram-isometry-Metric-Space :
    (n : ℕ) →
    isometry-Metric-Space
      ( seq-metric-space-sequential-diagram-isometry-Metric-Space X n)
      ( seq-metric-space-sequential-diagram-isometry-Metric-Space Z n)
  seq-isometry-comp-hom-sequential-diagram-isometry-Metric-Space n =
    comp-isometry-Metric-Space
      ( seq-metric-space-sequential-diagram-isometry-Metric-Space X n)
      ( seq-metric-space-sequential-diagram-isometry-Metric-Space Y n)
      ( seq-metric-space-sequential-diagram-isometry-Metric-Space Z n)
      ( seq-isometry-hom-sequential-diagram-isometry-Metric-Space Y Z h n)
      ( seq-isometry-hom-sequential-diagram-isometry-Metric-Space X Y f n)

  naturality-comp-hom-sequential-diagram-isometry-Metric-Space :
    naturality-hom-sequential-diagram-isometry-Metric-Space
      ( X)
      ( Z)
      ( seq-isometry-comp-hom-sequential-diagram-isometry-Metric-Space)
  naturality-comp-hom-sequential-diagram-isometry-Metric-Space =
    naturality-comp-hom-sequential-diagram
      ( diagram-sequential-diagram-isometry-Metric-Space X)
      ( diagram-sequential-diagram-isometry-Metric-Space Y)
      ( diagram-sequential-diagram-isometry-Metric-Space Z)
      ( hom-diagram-hom-sequential-diagram-isometry-Metric-Space Y Z h)
      ( hom-diagram-hom-sequential-diagram-isometry-Metric-Space X Y f)

  comp-hom-sequential-diagram-isometry-Metric-Space :
    hom-sequential-diagram-isometry-Metric-Space X Z
  comp-hom-sequential-diagram-isometry-Metric-Space =
    ( seq-isometry-comp-hom-sequential-diagram-isometry-Metric-Space ,
      naturality-comp-hom-sequential-diagram-isometry-Metric-Space)
```
