# Linear maps between normed real vector spaces

```agda
module linear-algebra.linear-maps-normed-real-vector-spaces where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.subtypes
open import foundation.universe-levels

open import linear-algebra.linear-maps-real-vector-spaces
open import linear-algebra.normed-real-vector-spaces
```

</details>

## Idea

A
{{#concept "linear map" Disambiguation="between two normed real vector spaces" Agda=linear-map-Normed-ℝ-Vector-Space}}
between [normed real vector spaces](linear-algebra.normed-real-vector-spaces.md)
`V` and `W` is a map `f : V → W` such that `f (v₁ + v₂) = f v₁ + f v₂` and
`f (c * v) ＝ c * f v`.

## Definition

```agda
module _
  {l1 l2 l3 : Level}
  (V@(VV , _) : Normed-ℝ-Vector-Space l1 l2)
  (W@(VW , _) : Normed-ℝ-Vector-Space l1 l3)
  where

  is-additive-map-prop-Normed-ℝ-Vector-Space :
    subtype
      ( l2 ⊔ l3)
      ( type-Normed-ℝ-Vector-Space V → type-Normed-ℝ-Vector-Space W)
  is-additive-map-prop-Normed-ℝ-Vector-Space =
    is-additive-map-prop-ℝ-Vector-Space VV VW

  is-additive-map-Normed-ℝ-Vector-Space :
    (type-Normed-ℝ-Vector-Space V → type-Normed-ℝ-Vector-Space W) → UU (l2 ⊔ l3)
  is-additive-map-Normed-ℝ-Vector-Space =
    is-additive-map-ℝ-Vector-Space VV VW

  is-homogeneous-map-prop-Normed-ℝ-Vector-Space :
    subtype
      ( lsuc l1 ⊔ l2 ⊔ l3)
      ( type-Normed-ℝ-Vector-Space V → type-Normed-ℝ-Vector-Space W)
  is-homogeneous-map-prop-Normed-ℝ-Vector-Space =
    is-homogeneous-map-prop-ℝ-Vector-Space VV VW

  is-homogeneous-map-Normed-ℝ-Vector-Space :
    (type-Normed-ℝ-Vector-Space V → type-Normed-ℝ-Vector-Space W) →
    UU (lsuc l1 ⊔ l2 ⊔ l3)
  is-homogeneous-map-Normed-ℝ-Vector-Space =
    is-homogeneous-map-ℝ-Vector-Space VV VW

  is-linear-map-prop-Normed-ℝ-Vector-Space :
    subtype
      ( lsuc l1 ⊔ l2 ⊔ l3)
      ( type-Normed-ℝ-Vector-Space V → type-Normed-ℝ-Vector-Space W)
  is-linear-map-prop-Normed-ℝ-Vector-Space =
    is-linear-map-prop-ℝ-Vector-Space VV VW

  is-linear-map-Normed-ℝ-Vector-Space :
    (type-Normed-ℝ-Vector-Space V → type-Normed-ℝ-Vector-Space W) →
    UU (lsuc l1 ⊔ l2 ⊔ l3)
  is-linear-map-Normed-ℝ-Vector-Space =
    is-linear-map-ℝ-Vector-Space VV VW

  linear-map-Normed-ℝ-Vector-Space : UU (lsuc l1 ⊔ l2 ⊔ l3)
  linear-map-Normed-ℝ-Vector-Space =
    type-subtype is-linear-map-prop-Normed-ℝ-Vector-Space

module _
  {l1 l2 l3 : Level}
  (V : Normed-ℝ-Vector-Space l1 l2)
  (W : Normed-ℝ-Vector-Space l1 l3)
  ((f , is-additive-f , is-homogeneous-f) :
    linear-map-Normed-ℝ-Vector-Space V W)
  where

  map-linear-map-Normed-ℝ-Vector-Space :
    type-Normed-ℝ-Vector-Space V → type-Normed-ℝ-Vector-Space W
  map-linear-map-Normed-ℝ-Vector-Space = f
```

## Properties

### A linear map maps zero to zero

```agda
module _
  {l1 l2 l3 : Level}
  (V : Normed-ℝ-Vector-Space l1 l2)
  (W : Normed-ℝ-Vector-Space l1 l3)
  (f : linear-map-Normed-ℝ-Vector-Space V W)
  where

  abstract
    is-zero-map-zero-linear-map-Normed-ℝ-Vector-Space :
      is-zero-Normed-ℝ-Vector-Space W
        ( map-linear-map-Normed-ℝ-Vector-Space V W
          ( f)
          ( zero-Normed-ℝ-Vector-Space V))
    is-zero-map-zero-linear-map-Normed-ℝ-Vector-Space =
      is-zero-map-zero-linear-map-ℝ-Vector-Space
        ( vector-space-Normed-ℝ-Vector-Space V)
        ( vector-space-Normed-ℝ-Vector-Space W)
        ( f)
```

### A linear map `f` maps `x - y` to `f x - f y`

```agda
module _
  {l1 l2 l3 : Level}
  (V : Normed-ℝ-Vector-Space l1 l2)
  (W : Normed-ℝ-Vector-Space l1 l3)
  (f : linear-map-Normed-ℝ-Vector-Space V W)
  where

  abstract
    map-diff-linear-map-Normed-ℝ-Vector-Space :
      {x y : type-Normed-ℝ-Vector-Space V} →
      map-linear-map-Normed-ℝ-Vector-Space V W f
        ( diff-Normed-ℝ-Vector-Space V x y) ＝
      diff-Normed-ℝ-Vector-Space W
        ( map-linear-map-Normed-ℝ-Vector-Space V W f x)
        ( map-linear-map-Normed-ℝ-Vector-Space V W f y)
    map-diff-linear-map-Normed-ℝ-Vector-Space =
      map-diff-linear-map-ℝ-Vector-Space
        ( vector-space-Normed-ℝ-Vector-Space V)
        ( vector-space-Normed-ℝ-Vector-Space W)
        ( f)
```
