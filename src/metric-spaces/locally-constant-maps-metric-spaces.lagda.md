# Locally constant maps in metric spaces

```agda
module metric-spaces.locally-constant-maps-metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.positive-rational-numbers

open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.equivalence-relations
open import foundation.existential-quantification
open import foundation.function-types
open import foundation.functoriality-propositional-truncation
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.sets
open import foundation.subtypes
open import foundation.universe-levels

open import metric-spaces.elements-at-bounded-distance-metric-spaces
open import metric-spaces.maps-metric-spaces
open import metric-spaces.metric-spaces
open import metric-spaces.short-maps-metric-spaces
```

</details>

## Idea

A [map](metric-spaces.maps-metric-spaces.md) between
[metric spaces](metric-spaces.metric-spaces.md) is
{{#concept "locally constant" Disambiguation="map between metric spaces" Agda=is-locally-constant-map-Metric-Space}}
if
[elements at bounded distance](metric-spaces.elements-at-bounded-distance-metric-spaces.md)
have [identical](foundation.identity-types.md) images. All locally constant maps
are [short](metric-spaces.short-maps-metric-spaces.md).

## Definitions

### The property of being a locally constant map

```agda
module _
  {l1 l2 l1' l2' : Level} (A : Metric-Space l1 l2) (B : Metric-Space l1' l2')
  (f : map-Metric-Space A B)
  where

  is-locally-constant-prop-map-Metric-Space : Prop (l1 ⊔ l2 ⊔ l1')
  is-locally-constant-prop-map-Metric-Space =
    Π-Prop
      ( type-Metric-Space A)
      ( λ x →
        Π-Prop
          ( type-Metric-Space A)
          ( λ y →
            bounded-dist-prop-Metric-Space A x y ⇒
            Id-Prop
              ( set-Metric-Space B)
              ( f x)
              ( f y)))

  is-locally-constant-map-Metric-Space : UU (l1 ⊔ l2 ⊔ l1')
  is-locally-constant-map-Metric-Space =
    type-Prop is-locally-constant-prop-map-Metric-Space

  abstract
    is-prop-is-locally-constant-map-Metric-Space :
      is-prop is-locally-constant-map-Metric-Space
    is-prop-is-locally-constant-map-Metric-Space =
      is-prop-type-Prop is-locally-constant-prop-map-Metric-Space
```

## Properties

### Locally constant maps are short

```agda
module _
  {l1 l2 l1' l2' : Level} (A : Metric-Space l1 l2) (B : Metric-Space l1' l2')
  (f : map-Metric-Space A B)
  where

  abstract
    is-short-map-is-locally-constant-map-Metric-Space :
      is-locally-constant-map-Metric-Space A B f →
      is-short-map-Metric-Space A B f
    is-short-map-is-locally-constant-map-Metric-Space H d x y Nxy =
      sim-eq-Metric-Space
        ( B)
        ( f x)
        ( f y)
        ( H x y (intro-exists d Nxy))
        ( d)
```
