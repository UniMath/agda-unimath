# Uniqueness of set truncations

```agda
module foundation.uniqueness-set-truncations where
```

<details><summary>Imports</summary>

```agda
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.functions
open import foundation.homotopies
open import foundation.mere-equality
open import foundation.sets
open import foundation.uniqueness-set-quotients
open import foundation.universal-property-set-truncation
open import foundation.universe-levels
```

</details>

## Idea

The universal property of set truncation implies that set truncations are uniquely unique.

## Properties

### A 3-for-2 property for set truncations

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} (B : Set l2) (f : A → type-Set B)
  (C : Set l3) (g : A → type-Set C) {h : type-hom-Set B C}
  (H : (h ∘ f) ~ g)
  where

  abstract
    is-equiv-is-set-truncation-is-set-truncation :
      ({l : Level} → is-set-truncation l B f) →
      ({l : Level} → is-set-truncation l C g) →
      is-equiv h
    is-equiv-is-set-truncation-is-set-truncation Sf Sg =
      is-equiv-is-set-quotient-is-set-quotient
        ( mere-eq-Eq-Rel A)
        ( B)
        ( reflecting-map-mere-eq B f)
        ( C)
        ( reflecting-map-mere-eq C g)
        ( H)
        ( λ {l} → is-set-quotient-is-set-truncation B f Sf)
        ( λ {l} → is-set-quotient-is-set-truncation C g Sg)

  abstract
    is-set-truncation-is-equiv-is-set-truncation :
      ({l : Level} → is-set-truncation l C g) → is-equiv h →
      {l : Level} → is-set-truncation l B f
    is-set-truncation-is-equiv-is-set-truncation Sg Eh =
      is-set-truncation-is-set-quotient B f
        ( is-set-quotient-is-equiv-is-set-quotient
          ( mere-eq-Eq-Rel A)
          ( B)
          ( reflecting-map-mere-eq B f)
          ( C)
          ( reflecting-map-mere-eq C g)
          ( H)
          ( is-set-quotient-is-set-truncation C g Sg)
          ( Eh))

  abstract
    is-set-truncation-is-set-truncation-is-equiv :
      is-equiv h → ({l : Level} → is-set-truncation l B f) →
      {l : Level} → is-set-truncation l C g
    is-set-truncation-is-set-truncation-is-equiv Eh Sf =
      is-set-truncation-is-set-quotient C g
        ( is-set-quotient-is-set-quotient-is-equiv
          ( mere-eq-Eq-Rel A)
          ( B)
          ( reflecting-map-mere-eq B f)
          ( C)
          ( reflecting-map-mere-eq C g)
          ( H)
          ( Eh)
          ( is-set-quotient-is-set-truncation B f Sf))
```

### The uniquely uniqueness of set truncations

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} (B : Set l2) (f : A → type-Set B)
  (C : Set l3) (g : A → type-Set C)
  (Sf : {l : Level} → is-set-truncation l B f)
  (Sg : {l : Level} → is-set-truncation l C g)
  where

  abstract
    uniqueness-set-truncation :
      is-contr (Σ (type-Set B ≃ type-Set C) (λ e → (map-equiv e ∘ f) ~ g))
    uniqueness-set-truncation =
      uniqueness-set-quotient
        ( mere-eq-Eq-Rel A)
        ( B)
        ( reflecting-map-mere-eq B f)
        ( is-set-quotient-is-set-truncation B f Sf)
        ( C)
        ( reflecting-map-mere-eq C g)
        ( is-set-quotient-is-set-truncation C g Sg)

  equiv-uniqueness-set-truncation : type-Set B ≃ type-Set C
  equiv-uniqueness-set-truncation =
    pr1 (center uniqueness-set-truncation)

  map-equiv-uniqueness-set-truncation : type-Set B → type-Set C
  map-equiv-uniqueness-set-truncation =
    map-equiv equiv-uniqueness-set-truncation

  triangle-uniqueness-set-truncation :
    (map-equiv-uniqueness-set-truncation ∘ f) ~ g
  triangle-uniqueness-set-truncation =
    pr2 (center uniqueness-set-truncation)
```
