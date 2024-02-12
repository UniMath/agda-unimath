# Pointed sections of pointed maps

```agda
module structured-types.pointed-sections where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import structured-types.pointed-homotopies
open import structured-types.pointed-maps
open import structured-types.pointed-types
```

</details>

## Idea

A {{#concept "pointed section" Disambiguation="pointed map" Agda=pointed-section-Pointed-Type}} of a [pointed map](structured-types.pointed-maps.md) `f : A →∗ B` consists of a pointed map
`g : B →∗ A` equipped with a [pointed homotopy](structured-types.pointed-homotopies.md) `H : (f ∘∗ g) ~∗ id`.

## Definitions

### The predicate of being a pointed section of a pointed map

```agda
module _
  {l1 l2 : Level} {A : Pointed-Type l1} {B : Pointed-Type l2} (f : A →∗ B)
  where


  is-pointed-section-Pointed-Type : (B →∗ A) → UU l2
  is-pointed-section-Pointed-Type g = f ∘∗ g ~∗ id-pointed-map
```

### The type of pointed sections of a pointed map

```agda
module _
  {l1 l2 : Level} {A : Pointed-Type l1} {B : Pointed-Type l2} (f : A →∗ B)
  where

  pointed-section-Pointed-Type : UU (l1 ⊔ l2)
  pointed-section-Pointed-Type =
    Σ (B →∗ A) (is-pointed-section-Pointed-Type f)
```
