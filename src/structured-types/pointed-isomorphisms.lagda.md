# Pointed isomorphisms

```agda
module structured-types.pointed-isomorphisms where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.retractions
open import foundation.sections
open import foundation.universe-levels

open import structured-types.pointed-homotopies
open import structured-types.pointed-maps
open import structured-types.pointed-retractions
open import structured-types.pointed-sections
open import structured-types.pointed-types
```

</details>

## Idea

A {{#concept "pointed isomorphism" Agda=pointed-iso}} is an isomorphism in the
wild category of pointed types, i.e., it is a
[pointed map](structured-types.pointed-types.md) equipped with a
[pointed section](structured-types.pointed-sections.md) and a
[pointed retraction](structured-types.pointed-retractions.md).

## Definitions

### The predicate of being a pointed isomorphism

```agda
module _
  {l1 l2 : Level} {A : Pointed-Type l1} {B : Pointed-Type l2} (f : A →∗ B)
  where

  is-pointed-iso : UU (l1 ⊔ l2)
  is-pointed-iso = pointed-section f × pointed-retraction f

module _
  {l1 l2 : Level} {A : Pointed-Type l1} {B : Pointed-Type l2} {f : A →∗ B}
  (H : is-pointed-iso f)
  where

  pointed-section-is-pointed-iso : pointed-section f
  pointed-section-is-pointed-iso = pr1 H

  pointed-retraction-is-pointed-iso : pointed-retraction f
  pointed-retraction-is-pointed-iso = pr2 H

  pointed-map-pointed-section-is-pointed-iso : B →∗ A
  pointed-map-pointed-section-is-pointed-iso =
    pointed-map-pointed-section f pointed-section-is-pointed-iso

  is-pointed-section-pointed-section-is-pointed-iso :
    is-pointed-section f pointed-map-pointed-section-is-pointed-iso
  is-pointed-section-pointed-section-is-pointed-iso =
    is-pointed-section-pointed-section f
      pointed-section-is-pointed-iso

  map-pointed-section-is-pointed-iso :
    type-Pointed-Type B → type-Pointed-Type A
  map-pointed-section-is-pointed-iso =
    map-pointed-section f pointed-section-is-pointed-iso

  preserves-point-pointed-map-pointed-section-is-pointed-iso :
    map-pointed-section-is-pointed-iso (point-Pointed-Type B) ＝
    point-Pointed-Type A
  preserves-point-pointed-map-pointed-section-is-pointed-iso =
    preserves-point-pointed-map-pointed-section f
      pointed-section-is-pointed-iso

  is-section-pointed-section-is-pointed-iso :
    is-section (map-pointed-map f) map-pointed-section-is-pointed-iso
  is-section-pointed-section-is-pointed-iso =
    is-section-pointed-section f pointed-section-is-pointed-iso

  section-is-pointed-iso :
    section (map-pointed-map f)
  section-is-pointed-iso =
    section-pointed-section f pointed-section-is-pointed-iso

  coherence-point-is-section-pointed-section-is-pointed-iso :
    coherence-point-unpointed-htpy-pointed-Π
      ( f ∘∗ pointed-map-pointed-section-is-pointed-iso)
      ( id-pointed-map)
      ( is-section-pointed-section-is-pointed-iso)
  coherence-point-is-section-pointed-section-is-pointed-iso =
    coherence-point-is-section-pointed-section f
      pointed-section-is-pointed-iso

  pointed-map-pointed-retraction-is-pointed-iso : B →∗ A
  pointed-map-pointed-retraction-is-pointed-iso =
    pr1 pointed-retraction-is-pointed-iso

  is-pointed-retraction-pointed-retraction-is-pointed-iso :
    is-pointed-retraction f pointed-map-pointed-retraction-is-pointed-iso
  is-pointed-retraction-pointed-retraction-is-pointed-iso =
    pr2 pointed-retraction-is-pointed-iso

  map-pointed-retraction-is-pointed-iso :
    type-Pointed-Type B → type-Pointed-Type A
  map-pointed-retraction-is-pointed-iso =
    map-pointed-map pointed-map-pointed-retraction-is-pointed-iso

  preserves-point-pointed-map-pointed-retraction-is-pointed-iso :
    map-pointed-retraction-is-pointed-iso (point-Pointed-Type B) ＝
    point-Pointed-Type A
  preserves-point-pointed-map-pointed-retraction-is-pointed-iso =
    preserves-point-pointed-map
      pointed-map-pointed-retraction-is-pointed-iso

  is-retraction-pointed-retraction-is-pointed-iso :
    is-retraction
      ( map-pointed-map f)
      ( map-pointed-retraction-is-pointed-iso)
  is-retraction-pointed-retraction-is-pointed-iso =
    htpy-pointed-htpy
      is-pointed-retraction-pointed-retraction-is-pointed-iso

  retraction-is-pointed-iso :
    retraction (map-pointed-map f)
  retraction-is-pointed-iso =
    retraction-pointed-retraction f pointed-retraction-is-pointed-iso

  coherence-point-is-retraction-pointed-retraction-is-pointed-iso :
    coherence-point-unpointed-htpy-pointed-Π
      ( pointed-map-pointed-retraction-is-pointed-iso ∘∗ f)
      ( id-pointed-map)
      ( is-retraction-pointed-retraction-is-pointed-iso)
  coherence-point-is-retraction-pointed-retraction-is-pointed-iso =
    coherence-point-pointed-htpy
      is-pointed-retraction-pointed-retraction-is-pointed-iso
```

### Pointed isomorphisms

```agda
module _
  {l1 l2 : Level} (A : Pointed-Type l1) (B : Pointed-Type l2)
  where

  pointed-iso : UU (l1 ⊔ l2)
  pointed-iso = Σ (A →∗ B) is-pointed-iso

  infix 6 _≅∗_

  _≅∗_ : UU (l1 ⊔ l2)
  _≅∗_ = pointed-iso

module _
  {l1 l2 : Level} (A : Pointed-Type l1) (B : Pointed-Type l2)
  (f : A ≅∗ B)
  where

  pointed-map-pointed-iso : A →∗ B
  pointed-map-pointed-iso = pr1 f

  map-pointed-iso : type-Pointed-Type A → type-Pointed-Type B
  map-pointed-iso = map-pointed-map pointed-map-pointed-iso

  preserves-point-pointed-iso :
    map-pointed-iso (point-Pointed-Type A) ＝ point-Pointed-Type B
  preserves-point-pointed-iso =
    preserves-point-pointed-map pointed-map-pointed-iso

  is-pointed-iso-pointed-iso : is-pointed-iso pointed-map-pointed-iso
  is-pointed-iso-pointed-iso = pr2 f

  pointed-section-pointed-iso : pointed-section pointed-map-pointed-iso
  pointed-section-pointed-iso =
    pointed-section-is-pointed-iso (is-pointed-iso-pointed-iso)

  pointed-retraction-pointed-iso : pointed-retraction pointed-map-pointed-iso
  pointed-retraction-pointed-iso =
    pointed-retraction-is-pointed-iso (is-pointed-iso-pointed-iso)

  pointed-map-pointed-section-pointed-iso : B →∗ A
  pointed-map-pointed-section-pointed-iso =
    pointed-map-pointed-section-is-pointed-iso (is-pointed-iso-pointed-iso)

  is-pointed-section-pointed-section-pointed-iso :
    is-pointed-section
      ( pointed-map-pointed-iso)
      ( pointed-map-pointed-section-pointed-iso)
  is-pointed-section-pointed-section-pointed-iso =
    is-pointed-section-pointed-section-is-pointed-iso
      ( is-pointed-iso-pointed-iso)

  map-pointed-section-pointed-iso :
    type-Pointed-Type B → type-Pointed-Type A
  map-pointed-section-pointed-iso =
    map-pointed-section-is-pointed-iso
      ( is-pointed-iso-pointed-iso)

  preserves-point-pointed-map-pointed-section-pointed-iso :
    map-pointed-section-pointed-iso (point-Pointed-Type B) ＝
    point-Pointed-Type A
  preserves-point-pointed-map-pointed-section-pointed-iso =
    preserves-point-pointed-map-pointed-section-is-pointed-iso
      ( is-pointed-iso-pointed-iso)

  is-section-pointed-section-pointed-iso :
    is-section (map-pointed-iso) map-pointed-section-pointed-iso
  is-section-pointed-section-pointed-iso =
    is-section-pointed-section-is-pointed-iso
      ( is-pointed-iso-pointed-iso)

  section-pointed-iso :
    section (map-pointed-iso)
  section-pointed-iso =
    section-is-pointed-iso
      ( is-pointed-iso-pointed-iso)

  coherence-point-is-section-pointed-section-pointed-iso :
    coherence-point-unpointed-htpy-pointed-Π
      ( pointed-map-pointed-iso ∘∗ pointed-map-pointed-section-pointed-iso)
      ( id-pointed-map)
      ( is-section-pointed-section-pointed-iso)
  coherence-point-is-section-pointed-section-pointed-iso =
    coherence-point-is-section-pointed-section-is-pointed-iso
      ( is-pointed-iso-pointed-iso)

  pointed-map-pointed-retraction-pointed-iso : B →∗ A
  pointed-map-pointed-retraction-pointed-iso =
    pointed-map-pointed-retraction-is-pointed-iso
      ( is-pointed-iso-pointed-iso)

  is-pointed-retraction-pointed-retraction-pointed-iso :
    is-pointed-retraction
      ( pointed-map-pointed-iso)
      ( pointed-map-pointed-retraction-pointed-iso)
  is-pointed-retraction-pointed-retraction-pointed-iso =
    is-pointed-retraction-pointed-retraction-is-pointed-iso
      ( is-pointed-iso-pointed-iso)

  map-pointed-retraction-pointed-iso :
    type-Pointed-Type B → type-Pointed-Type A
  map-pointed-retraction-pointed-iso =
    map-pointed-retraction-is-pointed-iso
      ( is-pointed-iso-pointed-iso)

  preserves-point-pointed-map-pointed-retraction-pointed-iso :
    map-pointed-retraction-pointed-iso (point-Pointed-Type B) ＝
    point-Pointed-Type A
  preserves-point-pointed-map-pointed-retraction-pointed-iso =
    preserves-point-pointed-map-pointed-retraction-is-pointed-iso
      ( is-pointed-iso-pointed-iso)

  is-retraction-pointed-retraction-pointed-iso :
    is-retraction
      ( map-pointed-iso)
      ( map-pointed-retraction-pointed-iso)
  is-retraction-pointed-retraction-pointed-iso =
    is-retraction-pointed-retraction-is-pointed-iso
      ( is-pointed-iso-pointed-iso)

  retraction-pointed-iso :
    retraction (map-pointed-iso)
  retraction-pointed-iso =
    retraction-is-pointed-iso
      ( is-pointed-iso-pointed-iso)

  coherence-point-is-retraction-pointed-retraction-pointed-iso :
    coherence-point-unpointed-htpy-pointed-Π
      ( pointed-map-pointed-retraction-pointed-iso ∘∗ pointed-map-pointed-iso)
      ( id-pointed-map)
      ( is-retraction-pointed-retraction-pointed-iso)
  coherence-point-is-retraction-pointed-retraction-pointed-iso =
    coherence-point-is-retraction-pointed-retraction-is-pointed-iso
      ( is-pointed-iso-pointed-iso)
```
