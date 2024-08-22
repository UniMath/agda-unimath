# Subsets of metric spaces

```agda
module metric-spaces.subsets-metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.logical-equivalences
open import foundation.subtypes
open import foundation.universe-levels

open import metric-spaces.functions-metric-spaces
open import metric-spaces.isometry-metric-spaces
open import metric-spaces.metric-spaces
open import metric-spaces.metric-structures
open import metric-spaces.neighbourhood-relations
```

</details>

## Idea

[Subsets](foundation.subtypes.md) of
[metric spaces](metric-spaces.metric-spaces.md) inherit the metric structure of
their ambient space. Moreover, the natural inclusion is
[isometric](metric-spaces.isometry-metric-spaces.md).

## Definitions

### Subsets of metric spaces

```agda
module _
  (l : Level) {l1 : Level} (A : Metric-Space l1)
  where

  subset-Metric-Space : UU (lsuc l ⊔ l1)
  subset-Metric-Space = subtype l (type-Metric-Space A)
```

## Properties

### Subsets of metric spaces inherit a metric structure

```agda
module _
  {l : Level} (A : Metric-Space l) (S : subset-Metric-Space l A)
  where

  substructure-Metric-Space : Metric-Structure l (type-subtype S)
  pr1 substructure-Metric-Space d x y =
    neighbourhood-Metric-Space A d (pr1 x) (pr1 y)
  pr2 substructure-Metric-Space =
    ( λ d x y → is-symmetric-neighbourhood-Metric-Space A d (pr1 x) (pr1 y)) ,
    ( λ d x → is-reflexive-neighbourhood-Metric-Space A d (pr1 x)) ,
    ( is-separating-is-tight-neighbourhood
      ( λ d x y → neighbourhood-Metric-Space A d (pr1 x) (pr1 y))
      ( λ x y H →
        eq-type-subtype
          ( S)
          ( is-tight-neighbourhood-Metric-Space A (pr1 x) (pr1 y) H))) ,
    ( λ x y z →
      is-triangular-neighbourhood-Metric-Space A (pr1 x) (pr1 y) (pr1 z))

  subspace-Metric-Space : Metric-Space l
  subspace-Metric-Space = (type-subtype S , substructure-Metric-Space)

  inclusion-subspace-Metric-Space :
    function-carrier-type-Metric-Space subspace-Metric-Space A
  inclusion-subspace-Metric-Space x = pr1 x
```

### The inclusion from a subspace in its ambient space is isometric

```agda
module _
  {l : Level} (A : Metric-Space l) (S : subset-Metric-Space l A)
  where

  is-isometry-inclusion-subspace-Metric-Space :
    is-isometry-function-Metric-Space
      (subspace-Metric-Space A S)
      (A)
      (inclusion-subspace-Metric-Space A S)
  is-isometry-inclusion-subspace-Metric-Space d x y = id-iff
```
