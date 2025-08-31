# Subsets of the real numbers

```agda
module real-numbers.subsets-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import foundation.images-subtypes
open import foundation.inhabited-subtypes
open import foundation.sets
open import foundation.subtypes
open import foundation.universe-levels

open import metric-spaces.metric-spaces
open import metric-spaces.subspaces-metric-spaces

open import real-numbers.dedekind-real-numbers
open import real-numbers.metric-space-of-real-numbers
```

</details>

## Idea

A {{#concept "subset" Disambiguation="of the real numbers" Agda=subset-ℝ}} of
the [real numbers](real-numbers.dedekind-real-numbers.md) is a
[subtype](foundation.subtypes.md).

## Definition

```agda
subset-ℝ : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
subset-ℝ l1 l2 = subtype l1 (ℝ l2)

type-subset-ℝ : {l1 l2 : Level} → subset-ℝ l1 l2 → UU (l1 ⊔ lsuc l2)
type-subset-ℝ = type-subtype

inclusion-subset-ℝ :
  {l1 l2 : Level} → (S : subset-ℝ l1 l2) → type-subset-ℝ S → ℝ l2
inclusion-subset-ℝ = inclusion-subtype

is-inhabited-subset-ℝ : {l1 l2 : Level} → subset-ℝ l1 l2 → UU (l1 ⊔ lsuc l2)
is-inhabited-subset-ℝ = is-inhabited-subtype
```

## Properties

### Subsets of the real numbers are sets

```agda
abstract
  is-set-subset-ℝ :
    {l1 l2 : Level} → (S : subset-ℝ l1 l2) → is-set (type-subset-ℝ S)
  is-set-subset-ℝ S = is-set-type-subtype S (is-set-type-Set (ℝ-Set _))
```

### The metric space associated with a subset of the real numbers

```agda
metric-space-subset-ℝ :
  {l1 l2 : Level} → subset-ℝ l1 l2 → Metric-Space (l1 ⊔ lsuc l2) l2
metric-space-subset-ℝ {l1} {l2} = subspace-Metric-Space (metric-space-ℝ l2)
```
