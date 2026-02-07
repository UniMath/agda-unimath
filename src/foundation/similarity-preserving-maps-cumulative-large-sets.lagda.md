# Similarity-preserving maps on cumulative large sets

```agda
module foundation.similarity-preserving-maps-cumulative-large-sets where
```

<details><summary>Imports</summary>

```agda
open import foundation.cumulative-large-sets
open import foundation.large-similarity-preserving-maps
open import foundation.identity-types
open import foundation.universe-levels
```

</details>

## Idea

Given [cumulative large sets](foundation.cumulative-large-sets.md) `X` and `Y`,
a map `f : X → Y`
{{#concept "preserves similarity" Disambiguation="map between two cumulative large sets" Agda=preserves-sim-map-Cumulative-Large-Set}}
if whenever `x₁` is similar to `x₂` , `f x₁` is similar to `f x₂`.

## Definition

```agda
module _
  {αX αY : Level → Level}
  {βX βY : Level → Level → Level}
  {X : (l : Level) → UU (αX l)}
  {Y : (l : Level) → UU (αY l)}
  (SX : Cumulative-Large-Set βX X)
  (SY : Cumulative-Large-Set βY Y)
  where

  preserves-sim-map-Cumulative-Large-Set :
    ({l : Level} → X l → Y l) → UUω
  preserves-sim-map-Cumulative-Large-Set f =
    preserves-sim-map-Large-Similarity-Relation
      ( large-similarity-relation-Cumulative-Large-Set SX)
      ( large-similarity-relation-Cumulative-Large-Set SY)
      ( f)

  sim-preserving-map-Cumulative-Large-Set : UUω
  sim-preserving-map-Cumulative-Large-Set =
    sim-preserving-map-Large-Similarity-Relation
      ( large-similarity-relation-Cumulative-Large-Set SX)
      ( large-similarity-relation-Cumulative-Large-Set SY)

  map-sim-preserving-map-Cumulative-Large-Set :
    sim-preserving-map-Cumulative-Large-Set → {l : Level} → X l → Y l
  map-sim-preserving-map-Cumulative-Large-Set =
    map-sim-preserving-map-Large-Similarity-Relation

  preserves-sim-map-sim-preserving-map-Cumulative-Large-Set :
    (f : sim-preserving-map-Cumulative-Large-Set) →
    preserves-sim-map-Cumulative-Large-Set
      ( map-sim-preserving-map-Cumulative-Large-Set f)
  preserves-sim-map-sim-preserving-map-Cumulative-Large-Set =
    preserves-sim-map-sim-preserving-map-Large-Similarity-Relation
```

### Similarity-preserving endomaps

```agda
module _
  {α : Level → Level}
  {β : Level → Level → Level}
  {X : (l : Level) → UU (α l)}
  (S : Cumulative-Large-Set β X)
  where

  preserves-sim-endomap-Cumulative-Large-Set : ({l : Level} → X l → X l) → UUω
  preserves-sim-endomap-Cumulative-Large-Set =
    preserves-sim-map-Cumulative-Large-Set S S

  sim-preserving-endomap-Cumulative-Large-Set : UUω
  sim-preserving-endomap-Cumulative-Large-Set =
    sim-preserving-map-Cumulative-Large-Set S S

  map-sim-preserving-endomap-Cumulative-Large-Set :
    sim-preserving-endomap-Cumulative-Large-Set → {l : Level} → X l → X l
  map-sim-preserving-endomap-Cumulative-Large-Set =
    map-sim-preserving-map-Large-Similarity-Relation

  preserves-sim-map-sim-preserving-endomap-Cumulative-Large-Set :
    (f : sim-preserving-endomap-Cumulative-Large-Set) →
    preserves-sim-endomap-Cumulative-Large-Set
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
  {X : (l : Level) → UU (αX l)}
  {Y : (l : Level) → UU (αY l)}
  (SX : Cumulative-Large-Set βX X)
  (SY : Cumulative-Large-Set βY Y)
  where

  abstract
    commute-map-raise-preserves-sim-map-Cumulative-Large-Set :
      (f : {l : Level} → X l → Y l) →
      preserves-sim-map-Cumulative-Large-Set SX SY f →
      {l1 : Level} (l2 : Level) (x : X l1) →
      f (raise-Cumulative-Large-Set SX l2 x) ＝
      raise-Cumulative-Large-Set SY l2 (f x)
    commute-map-raise-preserves-sim-map-Cumulative-Large-Set
      f preserves-sim-f {l1} l2 x =
      eq-sim-Cumulative-Large-Set SY
        ( transitive-sim-Cumulative-Large-Set SY _ _ _
          ( sim-raise-Cumulative-Large-Set SY l2 (f x))
          ( preserves-sim-f
            ( sim-raise-Cumulative-Large-Set' SX l2 x)))

module _
  {αX αY : Level → Level}
  {βX βY : Level → Level → Level}
  {X : (l : Level) → UU (αX l)}
  {Y : (l : Level) → UU (αY l)}
  (SX : Cumulative-Large-Set βX X)
  (SY : Cumulative-Large-Set βY Y)
  where

  abstract
    commute-map-raise-sim-preserving-map-Cumulative-Large-Set :
      (f : sim-preserving-map-Cumulative-Large-Set SX SY)
      {l0 : Level} (l : Level) (x : X l0) →
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
  {X : (l : Level) → UU (α l)}
  (S : Cumulative-Large-Set β X)
  where

  abstract
    commute-map-raise-sim-preserving-endomap-Cumulative-Large-Set :
      (f : sim-preserving-endomap-Cumulative-Large-Set S)
      {l0 : Level} (l : Level) (x : X l0) →
      map-sim-preserving-endomap-Cumulative-Large-Set S
        ( f)
        ( raise-Cumulative-Large-Set S l x) ＝
      raise-Cumulative-Large-Set S
        ( l)
        ( map-sim-preserving-endomap-Cumulative-Large-Set S f x)
    commute-map-raise-sim-preserving-endomap-Cumulative-Large-Set =
      commute-map-raise-sim-preserving-map-Cumulative-Large-Set S S
```

## See also

- [Similarity preserving binary maps between cumulative large sets](foundation.similarity-preserving-binary-maps-cumulative-large-sets.md)
