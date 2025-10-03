# The interior of subsets of metric spaces

```agda
module metric-spaces.interior-subsets-metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.positive-rational-numbers

open import foundation.dependent-pair-types
open import foundation.empty-subtypes
open import foundation.empty-types
open import foundation.existential-quantification
open import foundation.full-subtypes
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.raising-universe-levels
open import foundation.subtypes
open import foundation.unions-subtypes
open import foundation.unit-type
open import foundation.universe-levels

open import metric-spaces.metric-spaces
open import metric-spaces.subspaces-metric-spaces
```

</details>

## Idea

The
{{#concept "interior" disambiguation="of a subset of a metric space" WDID=Q862761 WD="interior" Agda=interior-subset-Metric-Space}}
of a [subset](foundation.subtypes.md) `S` of a
[metric space](metric-spaces.metric-spaces.md) `X` is the set of points `x` of
`X` where some neighborhood of `x` is contained in `S`.

## Definition

```agda
module _
  {l1 l2 l3 : Level} (X : Metric-Space l1 l2) (S : subset-Metric-Space l3 X)
  where

  interior-subset-Metric-Space : subset-Metric-Space (l1 ⊔ l2 ⊔ l3) X
  interior-subset-Metric-Space x =
    ∃ ℚ⁺ (λ ε → leq-prop-subtype (neighborhood-prop-Metric-Space X ε x) S)
```

## Properties

### The interior of `S` is a subset of `S`

```agda
module _
  {l1 l2 l3 : Level} (X : Metric-Space l1 l2) (S : subset-Metric-Space l3 X)
  where

  is-subset-interior-subset-Metric-Space :
    interior-subset-Metric-Space X S ⊆ S
  is-subset-interior-subset-Metric-Space x ∃ε =
    let open do-syntax-trunc-Prop (S x)
    in do
      (ε , Nεx⊆S) ← ∃ε
      Nεx⊆S x (refl-neighborhood-Metric-Space X ε x)
```

### The interior of the empty subset is empty

```agda
module _
  {l1 l2 : Level} (X : Metric-Space l1 l2)
  where

  is-empty-interior-empty-subset-Metric-Space :
    is-empty-subtype
      ( interior-subset-Metric-Space X (empty-subset-Metric-Space X))
  is-empty-interior-empty-subset-Metric-Space x ∃ε =
    let open do-syntax-trunc-Prop empty-Prop
    in do
      (ε , Nεx⊆∅) ← ∃ε
      map-inv-raise (Nεx⊆∅ x (refl-neighborhood-Metric-Space X ε x))
```

### The interior of the entire metric space is the metric space

```agda
  is-full-interior-full-subset-Metric-Space :
    is-full-subtype
      ( interior-subset-Metric-Space X (full-subset-Metric-Space X))
  is-full-interior-full-subset-Metric-Space x =
    intro-exists one-ℚ⁺ (λ _ _ → map-raise star)
```
