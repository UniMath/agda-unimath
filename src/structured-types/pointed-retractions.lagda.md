# Pointed retractions of pointed maps

```agda
module structured-types.pointed-retractions where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.retractions
open import foundation.universe-levels

open import structured-types.pointed-homotopies
open import structured-types.pointed-maps
open import structured-types.pointed-types
```

</details>

## Idea

A
{{#concept "pointed retraction" Disambiguation="pointed map" Agda=pointed-retraction}}
of a [pointed map](structured-types.pointed-maps.md) `f : A →∗ B` consists of a
pointed map `g : B →∗ A` equipped with a
[pointed homotopy](structured-types.pointed-homotopies.md) `H : g ∘∗ f ~∗ id`.

## Definitions

### The predicate of being a pointed retraction of a pointed map

```agda
module _
  {l1 l2 : Level} {A : Pointed-Type l1} {B : Pointed-Type l2} (f : A →∗ B)
  where


  is-pointed-retraction : (B →∗ A) → UU l1
  is-pointed-retraction g = g ∘∗ f ~∗ id-pointed-map
```

### The type of pointed retractions of a pointed map

```agda
module _
  {l1 l2 : Level} {A : Pointed-Type l1} {B : Pointed-Type l2} (f : A →∗ B)
  where

  pointed-retraction : UU (l1 ⊔ l2)
  pointed-retraction =
    Σ (B →∗ A) (is-pointed-retraction f)

  module _
    (s : pointed-retraction)
    where

    pointed-map-pointed-retraction : B →∗ A
    pointed-map-pointed-retraction = pr1 s

    is-pointed-retraction-pointed-retraction :
      is-pointed-retraction f pointed-map-pointed-retraction
    is-pointed-retraction-pointed-retraction = pr2 s

    map-pointed-retraction : type-Pointed-Type B → type-Pointed-Type A
    map-pointed-retraction = map-pointed-map pointed-map-pointed-retraction

    preserves-point-pointed-map-pointed-retraction :
      map-pointed-retraction (point-Pointed-Type B) ＝ point-Pointed-Type A
    preserves-point-pointed-map-pointed-retraction =
      preserves-point-pointed-map pointed-map-pointed-retraction

    is-retraction-pointed-retraction :
      is-retraction (map-pointed-map f) map-pointed-retraction
    is-retraction-pointed-retraction =
      htpy-pointed-htpy is-pointed-retraction-pointed-retraction

    retraction-pointed-retraction : retraction (map-pointed-map f)
    pr1 retraction-pointed-retraction = map-pointed-retraction
    pr2 retraction-pointed-retraction = is-retraction-pointed-retraction

    coherence-point-is-retraction-pointed-retraction :
      coherence-point-unpointed-htpy-pointed-Π
        ( pointed-map-pointed-retraction ∘∗ f)
        ( id-pointed-map)
        ( is-retraction-pointed-retraction)
    coherence-point-is-retraction-pointed-retraction =
      coherence-point-pointed-htpy is-pointed-retraction-pointed-retraction
```
