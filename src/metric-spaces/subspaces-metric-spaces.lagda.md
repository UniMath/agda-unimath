# Subspaces of metric spaces

```agda
module metric-spaces.subspaces-metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.logical-equivalences
open import foundation.subtypes
open import foundation.universe-levels

open import metric-spaces.functions-metric-spaces
open import metric-spaces.isometry-metric-spaces
open import metric-spaces.local-premetric-structures
open import metric-spaces.metric-spaces
open import metric-spaces.metric-structures
open import metric-spaces.monotonic-premetric-structures
open import metric-spaces.premetric-structures
open import metric-spaces.pseudometric-structures
open import metric-spaces.reflexive-premetric-structures
open import metric-spaces.symmetric-premetric-structures
open import metric-spaces.triangular-premetric-structures
```

</details>

## Idea

[Subsets](foundation.subtypes.md) of
[metric spaces](metric-spaces.metric-spaces.md) inherit the metric structure of
their ambient space. Moreover, the natural inclusion is an
[isometry](metric-spaces.isometry-metric-spaces.md).

## Definitions

### Subsets of metric spaces

```agda
module _
  (l : Level) {l1 l2 : Level} (A : Metric-Space l1 l2)
  where

  subset-Metric-Space : UU (lsuc l ⊔ l1)
  subset-Metric-Space = subtype l (type-Metric-Space A)
```

## Properties

### Subsets of metric spaces are metric spaces

```agda
module _
  {l l1 l2 : Level} (A : Metric-Space l1 l2)
  (S : subset-Metric-Space l A)
  where

  structure-subset-Metric-Space : Premetric l2 (type-subtype S)
  structure-subset-Metric-Space d x y =
    structure-Metric-Space A d (pr1 x) (pr1 y)

  is-reflexive-structure-subset-Metric-Space :
    is-reflexive-Premetric structure-subset-Metric-Space
  is-reflexive-structure-subset-Metric-Space d x =
    is-reflexive-premetric-structure-Metric-Space A d (pr1 x)

  is-symmetric-structure-subset-Metric-Space :
    is-symmetric-Premetric structure-subset-Metric-Space
  is-symmetric-structure-subset-Metric-Space d x y =
    is-symmetric-premetric-structure-Metric-Space A d (pr1 x) (pr1 y)

  is-triangular-structure-subset-Metric-Space :
    is-triangular-Premetric structure-subset-Metric-Space
  is-triangular-structure-subset-Metric-Space x y z =
    is-triangular-premetric-structure-Metric-Space A (pr1 x) (pr1 y) (pr1 z)

  is-pseudometric-structure-subset-Metric-Space :
    is-pseudometric-Premetric structure-subset-Metric-Space
  is-pseudometric-structure-subset-Metric-Space =
    is-reflexive-structure-subset-Metric-Space ,
    is-symmetric-structure-subset-Metric-Space ,
    is-triangular-structure-subset-Metric-Space

  is-metric-structure-subset-Metric-Space :
    is-metric-Premetric structure-subset-Metric-Space
  pr1 is-metric-structure-subset-Metric-Space =
    is-pseudometric-structure-subset-Metric-Space
  pr2 is-metric-structure-subset-Metric-Space =
    ( is-local-is-tight-Premetric
      ( structure-subset-Metric-Space)
      ( λ x y H →
        eq-type-subtype
          ( S)
          ( is-tight-premetric-structure-Metric-Space A (pr1 x) (pr1 y) H)))

  subspace-Metric-Space : Metric-Space (l ⊔ l1) l2
  pr1 subspace-Metric-Space =
    type-subtype S , structure-subset-Metric-Space
  pr2 subspace-Metric-Space =
    is-metric-structure-subset-Metric-Space

  inclusion-subspace-Metric-Space :
    function-carrier-type-Metric-Space subspace-Metric-Space A
  inclusion-subspace-Metric-Space = inclusion-subtype S
```

### The inclusion of a subspace is an isometry

```agda
module _
  {l l1 l2 : Level} (A : Metric-Space l1 l2) (S : subset-Metric-Space l A)
  where

  is-isometry-inclusion-subspace-Metric-Space :
    is-isometry-Metric-Space
      (subspace-Metric-Space A S)
      (A)
      (inclusion-subspace-Metric-Space A S)
  is-isometry-inclusion-subspace-Metric-Space d x y = id-iff
```
