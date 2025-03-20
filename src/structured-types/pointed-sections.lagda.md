# Pointed sections of pointed maps

```agda
open import foundation.function-extensionality-axiom

module
  structured-types.pointed-sections
  (funext : function-extensionality)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.identity-types funext
open import foundation.sections funext
open import foundation.universe-levels

open import structured-types.pointed-homotopies funext
open import structured-types.pointed-maps funext
open import structured-types.pointed-types
```

</details>

## Idea

A
{{#concept "pointed section" Disambiguation="pointed map" Agda=pointed-section}}
of a [pointed map](structured-types.pointed-maps.md) `f : A →∗ B` consists of a
pointed map `g : B →∗ A` equipped with a
[pointed homotopy](structured-types.pointed-homotopies.md) `H : f ∘∗ g ~∗ id`.

## Definitions

### The predicate of being a pointed section of a pointed map

```agda
module _
  {l1 l2 : Level} {A : Pointed-Type l1} {B : Pointed-Type l2} (f : A →∗ B)
  where

  is-pointed-section : (B →∗ A) → UU l2
  is-pointed-section g = f ∘∗ g ~∗ id-pointed-map
```

### The type of pointed sections of a pointed map

```agda
module _
  {l1 l2 : Level} {A : Pointed-Type l1} {B : Pointed-Type l2} (f : A →∗ B)
  where

  pointed-section : UU (l1 ⊔ l2)
  pointed-section =
    Σ (B →∗ A) (is-pointed-section f)

  module _
    (s : pointed-section)
    where

    pointed-map-pointed-section : B →∗ A
    pointed-map-pointed-section = pr1 s

    is-pointed-section-pointed-section :
      is-pointed-section f pointed-map-pointed-section
    is-pointed-section-pointed-section = pr2 s

    map-pointed-section : type-Pointed-Type B → type-Pointed-Type A
    map-pointed-section = map-pointed-map pointed-map-pointed-section

    preserves-point-pointed-map-pointed-section :
      map-pointed-section (point-Pointed-Type B) ＝ point-Pointed-Type A
    preserves-point-pointed-map-pointed-section =
      preserves-point-pointed-map pointed-map-pointed-section

    is-section-pointed-section :
      is-section (map-pointed-map f) map-pointed-section
    is-section-pointed-section =
      htpy-pointed-htpy is-pointed-section-pointed-section

    section-pointed-section : section (map-pointed-map f)
    pr1 section-pointed-section = map-pointed-section
    pr2 section-pointed-section = is-section-pointed-section

    coherence-point-is-section-pointed-section :
      coherence-point-unpointed-htpy-pointed-Π
        ( f ∘∗ pointed-map-pointed-section)
        ( id-pointed-map)
        ( is-section-pointed-section)
    coherence-point-is-section-pointed-section =
      coherence-point-pointed-htpy is-pointed-section-pointed-section
```
