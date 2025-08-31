# Subsets of the real numbers

```agda
module real-numbers.subsets-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import foundation.images-subtypes
open import foundation.inhabited-subtypes
open import foundation.action-on-identifications-functions
open import foundation.inhabited-types
open import foundation.functoriality-dependent-pair-types
open import foundation.transport-along-identifications
open import foundation.logical-equivalences
open import foundation.involutions
open import logic.functoriality-existential-quantification
open import foundation.propositional-truncations
open import foundation.identity-types
open import foundation.dependent-pair-types
open import foundation.sets
open import foundation.equivalences
open import foundation.subtypes
open import foundation.function-types
open import foundation.universe-levels
open import foundation.function-extensionality

open import metric-spaces.metric-spaces
open import metric-spaces.isometries-metric-spaces
open import metric-spaces.subspaces-metric-spaces
open import metric-spaces.equality-of-metric-spaces
open import metric-spaces.images-isometries-metric-spaces
open import real-numbers.isometry-negation-real-numbers

open import real-numbers.dedekind-real-numbers
open import real-numbers.negation-real-numbers
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

### The negation of a subset of real numbers

```agda
neg-subset-ℝ : {l1 l2 : Level} → subset-ℝ l1 l2 → subset-ℝ l1 l2
neg-subset-ℝ S = S ∘ neg-ℝ
```

### If a subset of real numbers is inhabited, so is its negation

```agda
abstract
  neg-is-inhabited-subset-ℝ :
    {l1 l2 : Level} → (S : subset-ℝ l1 l2) → is-inhabited-subset-ℝ S →
    is-inhabited-subset-ℝ (neg-subset-ℝ S)
  neg-is-inhabited-subset-ℝ S =
    map-exists
      ( is-in-subtype (neg-subset-ℝ S))
      ( neg-ℝ)
      ( λ s → inv-tr (is-in-subtype S) (neg-neg-ℝ s))
```

### The negation of the negation of a subset of real numbers is the original subset

```agda
abstract
  neg-neg-subset-ℝ :
    {l1 l2 : Level} → (S : subset-ℝ l1 l2) → neg-subset-ℝ (neg-subset-ℝ S) ＝ S
  neg-neg-subset-ℝ S = eq-htpy (λ x → ap S (neg-neg-ℝ x))
```

### The negation of a subset of real numbers is isometrically equivalent to the image of the subset under negation

```agda
module _
  {l1 l2 : Level} (S : subset-ℝ l1 l2)
  where

  equiv-isometric-equiv-neg-subset-im-neg-subset-ℝ :
    type-im-subtype neg-ℝ S ≃
    type-subtype (neg-subset-ℝ S)
  equiv-isometric-equiv-neg-subset-im-neg-subset-ℝ =
    equiv-has-same-elements-type-subtype
      ( im-subtype neg-ℝ S)
      ( neg-subset-ℝ S)
      ( has-same-elements-im-subtype-equiv-precomp-inv-equiv
        ( equiv-is-involution neg-neg-ℝ)
        ( S))

  is-isometry-map-equiv-isometric-equiv-neg-subset-im-neg-subset-ℝ :
    is-isometry-Metric-Space
      ( metric-space-subset-ℝ (im-subtype neg-ℝ S))
      ( metric-space-subset-ℝ (neg-subset-ℝ S))
      ( map-equiv equiv-isometric-equiv-neg-subset-im-neg-subset-ℝ)
  is-isometry-map-equiv-isometric-equiv-neg-subset-im-neg-subset-ℝ _ _ _ =
    id-iff

  isometric-equiv-neg-subset-im-neg-subset-ℝ :
    isometric-equiv-Metric-Space
      ( im-isometry-Metric-Space
        ( metric-space-subset-ℝ S)
        ( metric-space-ℝ l2)
        ( comp-isometry-Metric-Space
          ( metric-space-subset-ℝ S)
          ( metric-space-ℝ l2)
          ( metric-space-ℝ l2)
          ( isometry-neg-ℝ)
          ( isometry-inclusion-subspace-Metric-Space (metric-space-ℝ l2) S)))
      ( metric-space-subset-ℝ (neg-subset-ℝ S))
  isometric-equiv-neg-subset-im-neg-subset-ℝ =
    ( equiv-isometric-equiv-neg-subset-im-neg-subset-ℝ ,
      is-isometry-map-equiv-isometric-equiv-neg-subset-im-neg-subset-ℝ)
```
