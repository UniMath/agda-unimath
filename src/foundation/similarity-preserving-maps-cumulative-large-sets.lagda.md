# Similarity-preserving maps on cumulative large sets

```agda
module foundation.similarity-preserving-maps-cumulative-large-sets where
```

<details><summary>Imports</summary>

```agda
open import foundation.cumulative-large-sets
open import foundation.function-types
open import foundation.identity-types
open import foundation.similarity-preserving-maps-large-similarity-relations
open import foundation.universe-levels
```

</details>

## Idea

Given [cumulative large sets](foundation.cumulative-large-sets.md) on `X` and
`Y`, a map `f : X → Y`
{{#concept "preserves similarity" Disambiguation="map between two cumulative large sets" Agda=preserves-sim-map-Cumulative-Large-Set}}
if whenever `x₁` is similar to `x₂` , `f x₁` is similar to `f x₂`.

## Definition

```agda
module _
  {αX αY : Level → Level}
  {βX βY : Level → Level → Level}
  (γ : Level → Level)
  (SX : Cumulative-Large-Set αX βX)
  (SY : Cumulative-Large-Set αY βY)
  where

  preserves-sim-map-Cumulative-Large-Set :
    ( {l : Level} →
      type-Cumulative-Large-Set SX l →
      type-Cumulative-Large-Set SY (γ l)) → UUω
  preserves-sim-map-Cumulative-Large-Set f =
    preserves-sim-map-Large-Similarity-Relation
      ( large-similarity-relation-Cumulative-Large-Set SX)
      ( large-similarity-relation-Cumulative-Large-Set SY)
      ( f)

  sim-preserving-map-Cumulative-Large-Set : UUω
  sim-preserving-map-Cumulative-Large-Set =
    sim-preserving-map-Large-Similarity-Relation
      ( γ)
      ( large-similarity-relation-Cumulative-Large-Set SX)
      ( large-similarity-relation-Cumulative-Large-Set SY)

module _
  {αX αY γ : Level → Level}
  {βX βY : Level → Level → Level}
  (SX : Cumulative-Large-Set αX βX)
  (SY : Cumulative-Large-Set αY βY)
  where

  map-sim-preserving-map-Cumulative-Large-Set :
    sim-preserving-map-Cumulative-Large-Set γ SX SY →
    {l : Level} →
    type-Cumulative-Large-Set SX l → type-Cumulative-Large-Set SY (γ l)
  map-sim-preserving-map-Cumulative-Large-Set =
    map-sim-preserving-map-Large-Similarity-Relation

  preserves-sim-map-sim-preserving-map-Cumulative-Large-Set :
    (f : sim-preserving-map-Cumulative-Large-Set γ SX SY) →
    preserves-sim-map-Cumulative-Large-Set γ SX SY
      ( map-sim-preserving-map-Cumulative-Large-Set f)
  preserves-sim-map-sim-preserving-map-Cumulative-Large-Set =
    preserves-sim-map-sim-preserving-map-Large-Similarity-Relation
```

### Similarity-preserving endomaps

```agda
module _
  {α : Level → Level}
  {β : Level → Level → Level}
  (γ : Level → Level)
  (SX : Cumulative-Large-Set α β)
  where

  preserves-sim-endomap-Cumulative-Large-Set :
    ( {l : Level} →
      type-Cumulative-Large-Set SX l →
      type-Cumulative-Large-Set SX (γ l)) →
    UUω
  preserves-sim-endomap-Cumulative-Large-Set =
    preserves-sim-map-Cumulative-Large-Set γ SX SX

  sim-preserving-endomap-Cumulative-Large-Set : UUω
  sim-preserving-endomap-Cumulative-Large-Set =
    sim-preserving-map-Cumulative-Large-Set γ SX SX

module _
  {α γ : Level → Level}
  {β : Level → Level → Level}
  (SX : Cumulative-Large-Set α β)
  where

  map-sim-preserving-endomap-Cumulative-Large-Set :
    sim-preserving-endomap-Cumulative-Large-Set γ SX →
    {l : Level} →
    type-Cumulative-Large-Set SX l → type-Cumulative-Large-Set SX (γ l)
  map-sim-preserving-endomap-Cumulative-Large-Set =
    map-sim-preserving-map-Large-Similarity-Relation

  preserves-sim-map-sim-preserving-endomap-Cumulative-Large-Set :
    (f : sim-preserving-endomap-Cumulative-Large-Set γ SX) →
    preserves-sim-endomap-Cumulative-Large-Set γ SX
      ( map-sim-preserving-endomap-Cumulative-Large-Set f)
  preserves-sim-map-sim-preserving-endomap-Cumulative-Large-Set =
    preserves-sim-map-sim-preserving-map-Large-Similarity-Relation
```

## Properties

### Similarity-preserving maps commute with raising universe levels

```agda
module _
  {αX αY : Level → Level}
  {βX βY : Level → Level → Level}
  (SX : Cumulative-Large-Set αX βX)
  (SY : Cumulative-Large-Set αY βY)
  where

  abstract
    commute-map-raise-preserves-sim-map-Cumulative-Large-Set :
      ( f :
        {l : Level} →
        type-Cumulative-Large-Set SX l →
        type-Cumulative-Large-Set SY l) →
      preserves-sim-map-Cumulative-Large-Set id SX SY f →
      {l1 : Level} (l2 : Level) (x : type-Cumulative-Large-Set SX l1) →
      f (raise-Cumulative-Large-Set SX l2 x) ＝
      raise-Cumulative-Large-Set SY l2 (f x)
    commute-map-raise-preserves-sim-map-Cumulative-Large-Set
      f preserves-sim-f {l1} l2 x =
      eq-sim-Cumulative-Large-Set SY _ _
        ( transitive-sim-Cumulative-Large-Set SY _ _ _
          ( sim-raise-Cumulative-Large-Set SY l2 (f x))
          ( preserves-sim-f _ _ (sim-raise-Cumulative-Large-Set' SX l2 x)))

module _
  {αX αY : Level → Level}
  {βX βY : Level → Level → Level}
  (SX : Cumulative-Large-Set αX βX)
  (SY : Cumulative-Large-Set αY βY)
  where

  abstract
    commute-map-raise-sim-preserving-map-Cumulative-Large-Set :
      (f : sim-preserving-map-Cumulative-Large-Set id SX SY)
      {l0 : Level} (l : Level) (x : type-Cumulative-Large-Set SX l0) →
      map-sim-preserving-map-Cumulative-Large-Set SX SY
        ( f)
        ( raise-Cumulative-Large-Set SX l x) ＝
      raise-Cumulative-Large-Set SY
        ( l)
        ( map-sim-preserving-map-Cumulative-Large-Set SX SY f x)
    commute-map-raise-sim-preserving-map-Cumulative-Large-Set f =
      commute-map-raise-preserves-sim-map-Cumulative-Large-Set SX SY
        ( map-sim-preserving-map-Cumulative-Large-Set SX SY f)
        ( preserves-sim-map-sim-preserving-map-Cumulative-Large-Set SX SY f)

module _
  {α : Level → Level}
  {β : Level → Level → Level}
  (SX : Cumulative-Large-Set α β)
  where

  abstract
    commute-map-raise-sim-preserving-endomap-Cumulative-Large-Set :
      (f : sim-preserving-endomap-Cumulative-Large-Set id SX)
      {l0 : Level} (l : Level) (x : type-Cumulative-Large-Set SX l0) →
      map-sim-preserving-endomap-Cumulative-Large-Set SX
        ( f)
        ( raise-Cumulative-Large-Set SX l x) ＝
      raise-Cumulative-Large-Set SX
        ( l)
        ( map-sim-preserving-endomap-Cumulative-Large-Set SX f x)
    commute-map-raise-sim-preserving-endomap-Cumulative-Large-Set =
      commute-map-raise-sim-preserving-map-Cumulative-Large-Set SX SX
```

### Constructing a similarity-preserving map

```agda
module _
  {αX αY : Level → Level}
  {βX βY : Level → Level → Level}
  (γ : Level → Level)
  (SX : Cumulative-Large-Set αX βX)
  (SY : Cumulative-Large-Set αY βY)
  where

  make-sim-preserving-map-Cumulative-Large-Set :
    (f :
      {l : Level} →
      type-Cumulative-Large-Set SX l → type-Cumulative-Large-Set SY (γ l)) →
    preserves-sim-map-Cumulative-Large-Set γ SX SY f →
    sim-preserving-map-Cumulative-Large-Set γ SX SY
  make-sim-preserving-map-Cumulative-Large-Set f preserves-sim-f =
    λ where
      .map-sim-preserving-map-Large-Similarity-Relation →
        f
      .preserves-sim-map-sim-preserving-map-Large-Similarity-Relation →
        preserves-sim-f

module _
  {αX : Level → Level}
  {βX : Level → Level → Level}
  (γ : Level → Level)
  (SX : Cumulative-Large-Set αX βX)
  where

  make-sim-preserving-endomap-Cumulative-Large-Set :
    (f :
      {l : Level} →
      type-Cumulative-Large-Set SX l → type-Cumulative-Large-Set SX (γ l)) →
    preserves-sim-endomap-Cumulative-Large-Set γ SX f →
    sim-preserving-endomap-Cumulative-Large-Set γ SX
  make-sim-preserving-endomap-Cumulative-Large-Set =
    make-sim-preserving-map-Cumulative-Large-Set γ SX SX
```

## See also

- [Similarity preserving binary maps between cumulative large sets](foundation.similarity-preserving-binary-maps-cumulative-large-sets.md)
