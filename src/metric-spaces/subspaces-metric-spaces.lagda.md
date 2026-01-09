# Subspaces of metric spaces

```agda
module metric-spaces.subspaces-metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.empty-subtypes
open import foundation.full-subtypes
open import foundation.function-types
open import foundation.logical-equivalences
open import foundation.subtypes
open import foundation.universe-levels

open import metric-spaces.extensionality-pseudometric-spaces
open import metric-spaces.isometries-metric-spaces
open import metric-spaces.maps-metric-spaces
open import metric-spaces.metric-spaces
open import metric-spaces.pseudometric-spaces
open import metric-spaces.rational-neighborhood-relations
open import metric-spaces.reflexive-rational-neighborhood-relations
open import metric-spaces.saturated-rational-neighborhood-relations
open import metric-spaces.short-maps-metric-spaces
open import metric-spaces.symmetric-rational-neighborhood-relations
open import metric-spaces.triangular-rational-neighborhood-relations
open import metric-spaces.uniformly-continuous-maps-metric-spaces
```

</details>

## Idea

[Subsets](foundation.subtypes.md) of
[metric spaces](metric-spaces.metric-spaces.md) inherit the metric structure of
their ambient space; these are
{{#concept "metric subspaces" Agda=subspace-Metric-Space}} of metric spaces.

The natural inclusion of subspace into its ambient space is an
[isometry](metric-spaces.isometries-metric-spaces.md).

## Definitions

### Subsets of metric spaces

```agda
module _
  (l : Level) {l1 l2 : Level} (A : Metric-Space l1 l2)
  where

  subset-Metric-Space : UU (lsuc l ⊔ l1)
  subset-Metric-Space = subtype l (type-Metric-Space A)

module _
  {l1 l2 : Level} (A : Metric-Space l1 l2)
  where

  empty-subset-Metric-Space : subset-Metric-Space lzero A
  empty-subset-Metric-Space = empty-subtype lzero (type-Metric-Space A)

  full-subset-Metric-Space : subset-Metric-Space lzero A
  full-subset-Metric-Space = full-subtype lzero (type-Metric-Space A)
```

### Metric subspace of a metric space

```agda
module _
  {l l1 l2 : Level}
  (A : Metric-Space l1 l2)
  (S : subset-Metric-Space l A)
  where

  neighborhood-prop-subset-Metric-Space :
    Rational-Neighborhood-Relation l2 (type-subtype S)
  neighborhood-prop-subset-Metric-Space d x y =
    neighborhood-prop-Metric-Space A d (pr1 x) (pr1 y)

  is-reflexive-neighborhood-subset-Metric-Space :
    is-reflexive-Rational-Neighborhood-Relation
      neighborhood-prop-subset-Metric-Space
  is-reflexive-neighborhood-subset-Metric-Space d x =
    refl-neighborhood-Metric-Space A d (pr1 x)

  is-symmetric-neighborhood-subset-Metric-Space :
    is-symmetric-Rational-Neighborhood-Relation
      neighborhood-prop-subset-Metric-Space
  is-symmetric-neighborhood-subset-Metric-Space d x y =
    symmetric-neighborhood-Metric-Space A d (pr1 x) (pr1 y)

  is-triangular-neighborhood-subset-Metric-Space :
    is-triangular-Rational-Neighborhood-Relation
      neighborhood-prop-subset-Metric-Space
  is-triangular-neighborhood-subset-Metric-Space x y z =
    triangular-neighborhood-Metric-Space A (pr1 x) (pr1 y) (pr1 z)

  is-saturated-neighborhood-subset-Metric-Space :
    is-saturated-Rational-Neighborhood-Relation
      neighborhood-prop-subset-Metric-Space
  is-saturated-neighborhood-subset-Metric-Space ε x y =
    saturated-neighborhood-Metric-Space
      ( A)
      ( ε)
      ( pr1 x)
      ( pr1 y)

  pseudometric-subspace-Metric-Space :
    Pseudometric-Space (l ⊔ l1) l2
  pseudometric-subspace-Metric-Space =
    ( type-subtype S) ,
    ( neighborhood-prop-subset-Metric-Space ,
      is-reflexive-neighborhood-subset-Metric-Space ,
      is-symmetric-neighborhood-subset-Metric-Space ,
      is-triangular-neighborhood-subset-Metric-Space ,
      is-saturated-neighborhood-subset-Metric-Space)

  is-extensional-pseudometric-subspace-Metric-Space :
    is-extensional-Pseudometric-Space
      pseudometric-subspace-Metric-Space
  is-extensional-pseudometric-subspace-Metric-Space =
    is-extensional-is-tight-Pseudometric-Space
      ( pseudometric-subspace-Metric-Space)
      ( λ x y →
        eq-type-subtype S ∘
        eq-sim-Metric-Space A (pr1 x) (pr1 y))

  subspace-Metric-Space : Metric-Space (l ⊔ l1) l2
  subspace-Metric-Space =
    make-Metric-Space
      ( type-subtype S)
      ( neighborhood-prop-subset-Metric-Space)
      ( is-reflexive-neighborhood-subset-Metric-Space)
      ( is-symmetric-neighborhood-subset-Metric-Space)
      ( is-triangular-neighborhood-subset-Metric-Space)
      ( is-saturated-neighborhood-subset-Metric-Space)
      ( is-extensional-pseudometric-subspace-Metric-Space)
```

### Inclusion of a metric subspace into its ambient space

```agda
module _
  {l l1 l2 : Level}
  (A : Metric-Space l1 l2)
  (S : subset-Metric-Space l A)
  where

  inclusion-subspace-Metric-Space :
    map-Metric-Space
      ( subspace-Metric-Space A S)
      ( A)
  inclusion-subspace-Metric-Space = inclusion-subtype S
```

## Properties

### The inclusion of a subspace into its ambient space is an isometry

```agda
module _
  {l l1 l2 : Level}
  (A : Metric-Space l1 l2)
  (S : subset-Metric-Space l A)
  where

  is-isometry-inclusion-subspace-Metric-Space :
    is-isometry-Metric-Space
      (subspace-Metric-Space A S)
      (A)
      (inclusion-subspace-Metric-Space A S)
  is-isometry-inclusion-subspace-Metric-Space d x y = id-iff

  isometry-inclusion-subspace-Metric-Space :
    isometry-Metric-Space (subspace-Metric-Space A S) A
  isometry-inclusion-subspace-Metric-Space =
    inclusion-subspace-Metric-Space A S ,
    is-isometry-inclusion-subspace-Metric-Space
```

### The inclusion of a subspace into its ambient space is short

```agda
module _
  {l l1 l2 : Level}
  (A : Metric-Space l1 l2)
  (S : subset-Metric-Space l A)
  where

  short-inclusion-subspace-Metric-Space :
    short-map-Metric-Space (subspace-Metric-Space A S) A
  short-inclusion-subspace-Metric-Space =
    short-map-isometry-Metric-Space
      ( subspace-Metric-Space A S)
      ( A)
      ( isometry-inclusion-subspace-Metric-Space A S)
```

### The inclusion of a subspace into its ambient space is uniformly continuous

```agda
module _
  {l l1 l2 : Level}
  (A : Metric-Space l1 l2)
  (S : subset-Metric-Space l A)
  where

  uniformly-continuous-inclusion-subspace-Metric-Space :
    uniformly-continuous-map-Metric-Space (subspace-Metric-Space A S) A
  uniformly-continuous-inclusion-subspace-Metric-Space =
    uniformly-continuous-map-isometry-Metric-Space
      ( subspace-Metric-Space A S)
      ( A)
      ( isometry-inclusion-subspace-Metric-Space A S)
```

### If the images of a uniformly continuous function `f : X → Y` satisfy `P`, then `f` is a uniformly continuous function to the subspace of `Y` defined by `P`

```agda
module _
  {l1 l2 l3 l4 l5 : Level}
  (X : Metric-Space l1 l2)
  (Y : Metric-Space l3 l4)
  (P : subset-Metric-Space l5 Y)
  where

  uniformly-continuous-function-subspace-Metric-Space :
    (f : uniformly-continuous-function-Metric-Space X Y) →
    (Pf :
      (x : type-Metric-Space X) →
      is-in-subtype
        ( P)
        ( map-uniformly-continuous-function-Metric-Space X Y f x)) →
    uniformly-continuous-function-Metric-Space X (subspace-Metric-Space Y P)
  uniformly-continuous-function-subspace-Metric-Space (f , is-ucont-f) Pf =
    ( ( λ x → (f x , Pf x)) , is-ucont-f)
```
