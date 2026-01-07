# Pointwise continuous maps in metric spaces

```agda
module metric-spaces.pointwise-continuous-maps-metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.minimum-positive-rational-numbers
open import elementary-number-theory.positive-rational-numbers

open import foundation.cartesian-product-types
open import foundation.constant-maps
open import foundation.dependent-pair-types
open import foundation.existential-quantification
open import foundation.function-types
open import foundation.functoriality-cartesian-product-types
open import foundation.functoriality-propositional-truncation
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.subtypes
open import foundation.universe-levels

open import metric-spaces.cartesian-products-metric-spaces
open import metric-spaces.continuity-of-maps-at-points-metric-spaces
open import metric-spaces.maps-metric-spaces
open import metric-spaces.isometries-metric-spaces
open import metric-spaces.limits-of-maps-metric-spaces
open import metric-spaces.short-maps-metric-spaces
open import metric-spaces.metric-spaces
```

</details>

## Idea

A
{{#concept "pointwise continuous map" Disambiguation="between metric spaces" Agda=pointwise-continuous-map-Metric-Space}}
from a [metric space](metric-spaces.metric-spaces.md) `X` to a metric space `Y`
is a map `f : X → Y` which is
[continuous at every point](metric-spaces.continuity-of-maps-at-points-in-metric-spaces.md)
in `X`.

## Definition

```agda
module _
  {l1 l2 l3 l4 : Level}
  (X : Metric-Space l1 l2)
  (Y : Metric-Space l3 l4)
  (f : map-Metric-Space X Y)
  where

  is-pointwise-continuous-prop-map-Metric-Space : Prop (l1 ⊔ l2 ⊔ l4)
  is-pointwise-continuous-prop-map-Metric-Space =
    Π-Prop
      ( type-Metric-Space X)
      ( is-continuous-at-point-prop-map-Metric-Space X Y f)

  is-pointwise-continuous-map-Metric-Space : UU (l1 ⊔ l2 ⊔ l4)
  is-pointwise-continuous-map-Metric-Space =
    type-Prop is-pointwise-continuous-prop-map-Metric-Space

pointwise-continuous-map-Metric-Space :
  {l1 l2 l3 l4 : Level} → Metric-Space l1 l2 → Metric-Space l3 l4 →
  UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
pointwise-continuous-map-Metric-Space X Y =
  type-subtype (is-pointwise-continuous-prop-map-Metric-Space X Y)

module _
  {l1 l2 l3 l4 : Level}
  (X : Metric-Space l1 l2)
  (Y : Metric-Space l3 l4)
  (f : pointwise-continuous-map-Metric-Space X Y)
  where

  map-pointwise-continuous-map-Metric-Space : map-Metric-Space X Y
  map-pointwise-continuous-map-Metric-Space = pr1 f

  is-pointwise-continuous-map-pointwise-continuous-map-Metric-Space :
    is-pointwise-continuous-map-Metric-Space
      ( X)
      ( Y)
      ( map-pointwise-continuous-map-Metric-Space)
  is-pointwise-continuous-map-pointwise-continuous-map-Metric-Space = pr2 f
```

## Properties

### The Cartesian product of pointwise continuous maps on metric spaces

```agda
module _
  {l1 l2 l3 l4 l5 l6 l7 l8 : Level}
  (A : Metric-Space l1 l2) (B : Metric-Space l3 l4)
  (C : Metric-Space l5 l6) (D : Metric-Space l7 l8)
  (f : pointwise-continuous-map-Metric-Space A B)
  (g : pointwise-continuous-map-Metric-Space C D)
  where

  map-product-pointwise-continuous-map-Metric-Space :
    type-Metric-Space A × type-Metric-Space C →
    type-Metric-Space B × type-Metric-Space D
  map-product-pointwise-continuous-map-Metric-Space =
    map-product
      ( map-pointwise-continuous-map-Metric-Space A B f)
      ( map-pointwise-continuous-map-Metric-Space C D g)

  abstract
    is-pointwise-continuous-map-product-pointwise-continuous-map-Metric-Space :
      is-pointwise-continuous-map-Metric-Space
        ( product-Metric-Space A C)
        ( product-Metric-Space B D)
        ( map-product-pointwise-continuous-map-Metric-Space)
    is-pointwise-continuous-map-product-pointwise-continuous-map-Metric-Space
      ( a , c) =
      let
        open
          do-syntax-trunc-Prop
            ( is-point-limit-prop-map-Metric-Space
              ( product-Metric-Space A C)
              ( product-Metric-Space B D)
              ( map-product-pointwise-continuous-map-Metric-Space)
              ( a , c)
              ( map-product-pointwise-continuous-map-Metric-Space (a , c)))
      in do
        (μf , is-mod-μf) ←
          is-pointwise-continuous-map-pointwise-continuous-map-Metric-Space
            ( A)
            ( B)
            ( f)
            ( a)
        (μg , is-mod-μg) ←
          is-pointwise-continuous-map-pointwise-continuous-map-Metric-Space
            ( C)
            ( D)
            ( g)
            ( c)
        intro-exists
          ( λ ε → min-ℚ⁺ (μf ε) (μg ε))
          ( λ ε (a' , c') (Naa' , Ncc') →
            ( is-mod-μf
                ( ε)
                ( a')
                ( weakly-monotonic-neighborhood-Metric-Space
                  ( A)
                  ( a)
                  ( a')
                  ( min-ℚ⁺ (μf ε) (μg ε))
                  ( μf ε)
                  ( leq-left-min-ℚ⁺ (μf ε) (μg ε))
                  ( Naa')) ,
              is-mod-μg
                ( ε)
                ( c')
                ( weakly-monotonic-neighborhood-Metric-Space
                  ( C)
                  ( c)
                  ( c')
                  ( min-ℚ⁺ (μf ε) (μg ε))
                  ( μg ε)
                  ( leq-right-min-ℚ⁺ (μf ε) (μg ε))
                  ( Ncc'))))

  pointwise-continuous-map-product-Metric-Space :
    pointwise-continuous-map-Metric-Space
      ( product-Metric-Space A C)
      ( product-Metric-Space B D)
  pointwise-continuous-map-product-Metric-Space =
    ( map-product-pointwise-continuous-map-Metric-Space ,
      is-pointwise-continuous-map-product-pointwise-continuous-map-Metric-Space)
```

### The composition of pointwise continuous maps

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  (X : Metric-Space l1 l2)
  (Y : Metric-Space l3 l4)
  (Z : Metric-Space l5 l6)
  (f : pointwise-continuous-map-Metric-Space Y Z)
  (g : pointwise-continuous-map-Metric-Space X Y)
  where

  map-comp-pointwise-continuous-map-Metric-Space : map-Metric-Space X Z
  map-comp-pointwise-continuous-map-Metric-Space =
    map-pointwise-continuous-map-Metric-Space Y Z f ∘
    map-pointwise-continuous-map-Metric-Space X Y g

  abstract
    is-pointwise-continuous-map-comp-pointwise-continuous-map-Metric-Space :
      is-pointwise-continuous-map-Metric-Space X Z
        ( map-comp-pointwise-continuous-map-Metric-Space)
    is-pointwise-continuous-map-comp-pointwise-continuous-map-Metric-Space
      x =
      let
        open
          do-syntax-trunc-Prop
            ( is-point-limit-prop-map-Metric-Space X Z
              ( map-comp-pointwise-continuous-map-Metric-Space)
              ( x)
              ( map-comp-pointwise-continuous-map-Metric-Space x))
      in do
        (μg , is-mod-μg) ←
          is-pointwise-continuous-map-pointwise-continuous-map-Metric-Space
            ( X)
            ( Y)
            ( g)
            ( x)
        (μf , is-mod-μf) ←
          is-pointwise-continuous-map-pointwise-continuous-map-Metric-Space
            ( Y)
            ( Z)
            ( f)
            ( map-pointwise-continuous-map-Metric-Space X Y g x)
        intro-exists
          ( μg ∘ μf)
          ( λ ε x' Nxx' →
            is-mod-μf
              ( ε)
              ( map-pointwise-continuous-map-Metric-Space X Y g x')
              ( is-mod-μg (μf ε) x' Nxx'))

  comp-pointwise-continuous-map-Metric-Space :
    pointwise-continuous-map-Metric-Space X Z
  comp-pointwise-continuous-map-Metric-Space =
    ( map-comp-pointwise-continuous-map-Metric-Space ,
      is-pointwise-continuous-map-comp-pointwise-continuous-map-Metric-Space)
```

### Isometries are pointwise continuous

```agda
module _
  {l1 l2 l3 l4 : Level}
  (X : Metric-Space l1 l2)
  (Y : Metric-Space l3 l4)
  where

  abstract
    is-pointwise-continuous-map-is-isometry-Metric-Space :
      (f : map-Metric-Space X Y) →
      is-isometry-Metric-Space X Y f →
      is-pointwise-continuous-map-Metric-Space X Y f
    is-pointwise-continuous-map-is-isometry-Metric-Space
      f H =
      is-pointwise-continuous-is-uniformly-continuous-map-Metric-Space
        ( X)
        ( Y)
        ( f)
        ( is-uniformly-continuous-is-isometry-Metric-Space X Y f H)

  pointwise-continuous-map-isometry-Metric-Space :
    isometry-Metric-Space X Y →
    pointwise-continuous-map-Metric-Space X Y
  pointwise-continuous-map-isometry-Metric-Space (f , H) =
    ( f ,
      is-pointwise-continuous-map-is-isometry-Metric-Space f H)
```

### Constant maps between metric spaces are pointwise continuous

```agda
module _
  {l1 l2 l3 l4 : Level}
  (X : Metric-Space l1 l2)
  (Y : Metric-Space l3 l4)
  (y : type-Metric-Space Y)
  where

  abstract
    is-pointwise-continuous-map-const-Metric-Space :
      is-pointwise-continuous-map-Metric-Space
        ( X)
        ( Y)
        ( const-map-Metric-Space X y)
    is-pointwise-continuous-map-const-Metric-Space =
      is-pointwise-continuous-map-is-short-map-Metric-Space X Y _
        ( is-short-constant-map-Metric-Space X Y y)

  const-pointwise-continuous-map-Metric-Space :
    pointwise-continuous-map-Metric-Space X Y
  const-pointwise-continuous-map-Metric-Space =
    pointwise-continuous-map-short-map-Metric-Space X Y
      ( short-constant-map-Metric-Space X Y y)
```

### The identity map is a pointwise continuous map on any metric space

```agda
module _
  {l1 l2 : Level}
  (X : Metric-Space l1 l2)
  where

  abstract
    is-pointwise-continuous-map-id-Metric-Space :
      is-pointwise-continuous-map-Metric-Space X X id
    is-pointwise-continuous-map-id-Metric-Space =
      is-pointwise-continuous-map-is-isometry-Metric-Space X X id
        ( is-isometry-id-Metric-Space X)

  id-pointwise-continuous-map-Metric-Space :
    pointwise-continuous-map-Metric-Space X X
  id-pointwise-continuous-map-Metric-Space =
    ( id , is-pointwise-continuous-map-id-Metric-Space)
```

### Short maps are pointwise continuous

```agda
module _
  {l1 l2 l3 l4 : Level}
  (X : Metric-Space l1 l2)
  (Y : Metric-Space l3 l4)
  where

  abstract
    is-pointwise-continuous-map-is-short-map-Metric-Space :
      (f : map-Metric-Space X Y) →
      is-short-map-Metric-Space X Y f →
      is-pointwise-continuous-map-Metric-Space X Y f
    is-pointwise-continuous-map-is-short-map-Metric-Space
      f H =
      ?

  pointwise-continuous-map-short-map-Metric-Space :
    short-map-Metric-Space X Y →
    pointwise-continuous-map-Metric-Space X Y
  pointwise-continuous-map-short-map-Metric-Space (f , H) =
    ( f ,
      is-pointwise-continuous-map-is-short-map-Metric-Space f H)
```

## See also

- [ε-δ pointwise continuous maps in metric spaces](metric-spaces.pointwise-epsilon-delta-continuous-maps-metric-spaces.md)
