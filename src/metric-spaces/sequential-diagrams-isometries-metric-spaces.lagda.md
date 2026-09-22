# Sequential diagrams of isometries between metric spaces

```agda
module metric-spaces.sequential-diagrams-isometries-metric-spaces where
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

open import synthetic-homotopy-theory.sequential-diagrams
```

</details>

## Idea

A
{{#concept "sequential diagram of isometries between metric spaces" Agda=sequential-diagram-isometry-Metric-Space}}
is a [sequence](lists.sequences.md) of
[metric spaces](metric-spaces.metric-spaces.md) `M : ℕ → Metric-Space` equipped
with a sequence of isometries `fₙ : Mₙ → Mₙ₊₁` for all `n : ℕ`.

They can be represented by diagrams of isometries

```text
     f₀       f₁       f₂
 M₀ ----> M₁ ----> M₂ ----> ⋯
```

extending infinitely to the right.

## Definitions

### Sequential diagrams of isometries

```agda
seq-isometry-sequence-Metric-Space :
  {l1 l2 : Level} → (ℕ → Metric-Space l1 l2) → UU (l1 ⊔ l2)
seq-isometry-sequence-Metric-Space M =
  (n : ℕ) → isometry-Metric-Space (M n) (M (succ-ℕ n))

sequential-diagram-isometry-Metric-Space :
  (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
sequential-diagram-isometry-Metric-Space l1 l2 =
  Σ (ℕ → Metric-Space l1 l2) seq-isometry-sequence-Metric-Space

module _
  {l1 l2 : Level} (M : sequential-diagram-isometry-Metric-Space l1 l2)
  where

  seq-metric-space-sequential-diagram-isometry-Metric-Space :
    (n : ℕ) → Metric-Space l1 l2
  seq-metric-space-sequential-diagram-isometry-Metric-Space = pr1 M

  family-sequential-diagram-isometry-Metric-Space : (n : ℕ) → UU l1
  family-sequential-diagram-isometry-Metric-Space n =
    type-Metric-Space
      (seq-metric-space-sequential-diagram-isometry-Metric-Space n)

  seq-isometry-sequential-diagram-isometry-Metric-Space :
    seq-isometry-sequence-Metric-Space
      seq-metric-space-sequential-diagram-isometry-Metric-Space
  seq-isometry-sequential-diagram-isometry-Metric-Space = pr2 M

  seq-map-isometry-sequential-diagram-isometry-Metric-Space :
    (n : ℕ) →
    family-sequential-diagram-isometry-Metric-Space n →
    family-sequential-diagram-isometry-Metric-Space (succ-ℕ n)
  seq-map-isometry-sequential-diagram-isometry-Metric-Space n =
    map-isometry-Metric-Space
      ( seq-metric-space-sequential-diagram-isometry-Metric-Space n)
      ( seq-metric-space-sequential-diagram-isometry-Metric-Space (succ-ℕ n))
      ( seq-isometry-sequential-diagram-isometry-Metric-Space n)

  diagram-sequential-diagram-isometry-Metric-Space : sequential-diagram l1
  diagram-sequential-diagram-isometry-Metric-Space =
    ( family-sequential-diagram-isometry-Metric-Space ,
      seq-map-isometry-sequential-diagram-isometry-Metric-Space)
```

### Total space of a sequential diagram

```agda
module _
  {l1 l2 : Level} (M : sequential-diagram-isometry-Metric-Space l1 l2)
  where

  tot-metric-space-sequential-diagram-isometry-Metric-Space : Metric-Space l1 l2
  tot-metric-space-sequential-diagram-isometry-Metric-Space =
    indexed-sum-Metric-Space
      ( ℕ-Set)
      ( seq-metric-space-sequential-diagram-isometry-Metric-Space M)

  seq-isometry-tot-metric-space-sequential-diagram-isometry-Metric-Space :
    (n : ℕ) →
    isometry-Metric-Space
      ( seq-metric-space-sequential-diagram-isometry-Metric-Space M n)
      ( tot-metric-space-sequential-diagram-isometry-Metric-Space)
  seq-isometry-tot-metric-space-sequential-diagram-isometry-Metric-Space =
    isometry-emb-fiber-indexed-Metric-Space
      ( ℕ-Set)
      ( seq-metric-space-sequential-diagram-isometry-Metric-Space M)

  seq-map-tot-metric-space-sequential-diagram-isometry-Metric-Space :
    (n : ℕ) →
    family-sequential-diagram-isometry-Metric-Space M n →
    Σ ℕ (family-sequential-diagram-isometry-Metric-Space M)
  seq-map-tot-metric-space-sequential-diagram-isometry-Metric-Space n =
    map-isometry-Metric-Space
      ( seq-metric-space-sequential-diagram-isometry-Metric-Space M n)
      ( tot-metric-space-sequential-diagram-isometry-Metric-Space)
      ( seq-isometry-tot-metric-space-sequential-diagram-isometry-Metric-Space
        ( n))
```
