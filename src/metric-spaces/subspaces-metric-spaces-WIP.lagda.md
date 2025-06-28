# Subspaces of metric spaces (WIP)

```agda
module metric-spaces.subspaces-metric-spaces-WIP where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.logical-equivalences
open import foundation.subtypes
open import foundation.universe-levels

open import metric-spaces.extensional-pseudometric-spaces-WIP
open import metric-spaces.isometries-metric-spaces-WIP
open import metric-spaces.metric-spaces-WIP
open import metric-spaces.pseudometric-spaces-WIP
open import metric-spaces.rational-neighborhoods
open import metric-spaces.reflexive-rational-neighborhoods
open import metric-spaces.saturated-rational-neighborhoods
open import metric-spaces.symmetric-rational-neighborhoods
open import metric-spaces.triangular-rational-neighborhoods
```

</details>

## Idea

[Subsets](foundation.subtypes.md) of
[metric spaces](metric-spaces.metric-spaces.md) inherit the metric structure of
their ambient space; these are
{{#concept "metric subspaces" Agda=subspace-Metric-Space-WIP}} of metric spaces.

The natural inclusion of subspace into its ambient space is an
[isometry](metric-spaces.isometries-metric-spaces.md).

## Definitions

### Subsets of metric spaces

```agda
module _
  (l : Level) {l1 l2 : Level} (A : Metric-Space-WIP l1 l2)
  where

  subset-Metric-Space-WIP : UU (lsuc l ⊔ l1)
  subset-Metric-Space-WIP = subtype l (type-Metric-Space-WIP A)
```

### Metric subspace of a metric space

```agda
module _
  {l l1 l2 : Level}
  (A : Metric-Space-WIP l1 l2)
  (S : subset-Metric-Space-WIP l A)
  where

  neighborhood-prop-subset-Metric-Space-WIP :
    Rational-Neighborhood-Relation l2 (type-subtype S)
  neighborhood-prop-subset-Metric-Space-WIP d x y =
    neighborhood-prop-Metric-Space-WIP A d (pr1 x) (pr1 y)

  is-reflexive-neighborhood-subset-Metric-Space-WIP :
    is-reflexive-Rational-Neighborhood-Relation
      neighborhood-prop-subset-Metric-Space-WIP
  is-reflexive-neighborhood-subset-Metric-Space-WIP d x =
    refl-neighborhood-Metric-Space-WIP A d (pr1 x)

  is-symmetric-neighborhood-subset-Metric-Space-WIP :
    is-symmetric-Rational-Neighborhood-Relation
      neighborhood-prop-subset-Metric-Space-WIP
  is-symmetric-neighborhood-subset-Metric-Space-WIP d x y =
    symmetric-neighborhood-Metric-Space-WIP A d (pr1 x) (pr1 y)

  is-triangular-neighborhood-subset-Metric-Space-WIP :
    is-triangular-Rational-Neighborhood-Relation
      neighborhood-prop-subset-Metric-Space-WIP
  is-triangular-neighborhood-subset-Metric-Space-WIP x y z =
    triangular-neighborhood-Metric-Space-WIP A (pr1 x) (pr1 y) (pr1 z)

  is-saturated-neighborhood-subset-Metric-Space-WIP :
    is-saturated-Rational-Neighborhood-Relation
      neighborhood-prop-subset-Metric-Space-WIP
  is-saturated-neighborhood-subset-Metric-Space-WIP ε x y =
    saturated-neighborhood-Metric-Space-WIP
      ( A)
      ( ε)
      ( pr1 x)
      ( pr1 y)

  pseudometric-subspace-Metric-Space-WIP :
    Pseudometric-Space-WIP (l ⊔ l1) l2
  pseudometric-subspace-Metric-Space-WIP =
    ( type-subtype S) ,
    ( neighborhood-prop-subset-Metric-Space-WIP ,
      is-reflexive-neighborhood-subset-Metric-Space-WIP ,
      is-symmetric-neighborhood-subset-Metric-Space-WIP ,
      is-triangular-neighborhood-subset-Metric-Space-WIP ,
      is-saturated-neighborhood-subset-Metric-Space-WIP)

  is-extensional-pseudometric-subspace-Metric-Space-WIP :
    is-extensional-Pseudometric-Space-WIP
      pseudometric-subspace-Metric-Space-WIP
  is-extensional-pseudometric-subspace-Metric-Space-WIP =
    is-extensional-is-tight-Pseudometric-Space
      ( pseudometric-subspace-Metric-Space-WIP)
      ( λ x y →
        eq-type-subtype S ∘
        eq-sim-Metric-Space-WIP A (pr1 x) (pr1 y))

  subspace-Metric-Space-WIP : Metric-Space-WIP (l ⊔ l1) l2
  subspace-Metric-Space-WIP =
    pseudometric-subspace-Metric-Space-WIP ,
    is-extensional-pseudometric-subspace-Metric-Space-WIP
```

### Inclusion of a metric subspace into its ambient space

```agda
module _
  {l l1 l2 : Level}
  (A : Metric-Space-WIP l1 l2)
  (S : subset-Metric-Space-WIP l A)
  where

  inclusion-subspace-Metric-Space-WIP :
    type-function-Metric-Space-WIP
      ( subspace-Metric-Space-WIP A S)
      ( A)
  inclusion-subspace-Metric-Space-WIP = inclusion-subtype S
```

## Properties

### The inclusion of a subspace into its ambient space is an isometry

```agda
module _
  {l l1 l2 : Level}
  (A : Metric-Space-WIP l1 l2)
  (S : subset-Metric-Space-WIP l A)
  where

  is-isometry-inclusion-subspace-Metric-Space-WIP :
    is-isometry-Metric-Space-WIP
      (subspace-Metric-Space-WIP A S)
      (A)
      (inclusion-subspace-Metric-Space-WIP A S)
  is-isometry-inclusion-subspace-Metric-Space-WIP d x y = id-iff

  isometry-inclusion-subspace-Metric-Space-WIP :
    isometry-Metric-Space-WIP (subspace-Metric-Space-WIP A S) A
  isometry-inclusion-subspace-Metric-Space-WIP =
    inclusion-subspace-Metric-Space-WIP A S ,
    is-isometry-inclusion-subspace-Metric-Space-WIP
```
