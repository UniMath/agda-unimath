# Equality of metric spaces

```agda
module metric-spaces.equality-of-metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.binary-relations
open import foundation.binary-transport
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equality-dependent-pair-types
open import foundation.equivalences
open import foundation.fibers-of-maps
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.propositions
open import foundation.subtypes
open import foundation.torsorial-type-families
open import foundation.transport-along-identifications
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.univalence
open import foundation.universe-levels

open import metric-spaces.functions-metric-spaces
open import metric-spaces.isometry-metric-spaces
open import metric-spaces.metric-spaces
open import metric-spaces.metric-structures
open import metric-spaces.neighbourhood-relations
open import metric-spaces.transport-of-metric-structures
```

</details>

## Idea

Two [metric-spaces](metric-spaces.metric-spaces.md) with equal carrier types are
equal if the natural induced map between the carrier types is an
[isometry](metric-spaces.isometry-metric-spaces.md).

## Definitions

### An equality between carrier types is isometric if its natural induced map is an isometry

```agda
module _
  {l : Level} (A B : Metric-Space l)
  where

  is-isometric-eq-prop-Metric-Space :
    (type-Metric-Space A ＝ type-Metric-Space B) → Prop l
  is-isometric-eq-prop-Metric-Space e =
    is-isometry-prop-function-Metric-Space A B (map-eq e)

  is-isometric-eq-Metric-Space :
    (type-Metric-Space A ＝ type-Metric-Space B) → UU l
  is-isometric-eq-Metric-Space e =
    type-Prop (is-isometric-eq-prop-Metric-Space e)

  is-prop-is-isomeetric-eq-Metric-Space :
    (e : type-Metric-Space A ＝ type-Metric-Space B) →
    is-prop (is-isometric-eq-Metric-Space e)
  is-prop-is-isomeetric-eq-Metric-Space e =
    is-prop-type-Prop (is-isometric-eq-prop-Metric-Space e)

  isometric-eq-Metric-Space : UU (lsuc l)
  isometric-eq-Metric-Space = type-subtype is-isometric-eq-prop-Metric-Space
```

## Properties

### An equality between carrier types of metric spaces transport the metric structures if and only if is it isometric

```agda
module _
  {l : Level} (A B : Metric-Space l)
  (e : type-Metric-Space A ＝ type-Metric-Space B)
  where

  equiv-is-isometry-map-eq-tr-Metric-Structure :
    Id
      ( tr (Metric-Structure l) e (structure-Metric-Space A))
      ( structure-Metric-Space B) ≃
    is-isometry-function-Metric-Space A B (map-eq e)
  equiv-is-isometry-map-eq-tr-Metric-Structure =
    ( equiv-is-isometry-map-eq-Eq-tr-Metric-Structure
      ( type-Metric-Space A)
      ( type-Metric-Space B)
      ( e)
      ( structure-Metric-Space A)
      ( structure-Metric-Space B)) ∘e
    ( equiv-Eq-eq-Metric-Structure
      ( type-Metric-Space B)
      ( tr (Metric-Structure l) e (structure-Metric-Space A))
      ( structure-Metric-Space B))
```

### Equality of metric spaces is equivalent to isometric equality of their carrier types

```agda
module _
  {l : Level} (A B : Metric-Space l)
  where

  equiv-isometric-eq-Metric-Space : (A ＝ B) ≃ isometric-eq-Metric-Space A B
  equiv-isometric-eq-Metric-Space =
    ( equiv-tot (equiv-is-isometry-map-eq-tr-Metric-Structure A B)) ∘e
    ( equiv-pair-eq-Σ A B)
```

### Isometric equality is torsorial

```agda
module _
  {l : Level} (A : Metric-Space l)
  where

  is-torsorial-isometric-eq-Metric-Space :
    is-torsorial (isometric-eq-Metric-Space A)
  is-torsorial-isometric-eq-Metric-Space =
    is-contr-equiv'
      ( Σ (Metric-Space l) (Id A))
      ( equiv-tot (equiv-isometric-eq-Metric-Space A))
      ( is-torsorial-Id A)
```
