# The flat modality's action on homotopies

```agda
{-# OPTIONS --cohesion --flat-split #-}

module modal-type-theory.flat-action-on-homotopies where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.injective-maps
open import foundation.retractions
open import foundation.retracts-of-types
open import foundation.sections
open import foundation.torsorial-type-families
open import foundation.universe-levels

open import modal-type-theory.crisp-identity-types
open import modal-type-theory.flat-modality
open import modal-type-theory.functoriality-flat-modality
```

</details>

## Idea

Given a crisp [homotopy](foundation-core.homotopies.md) of maps `f ~ g`, then
there is a homotopy `♭ f ~ ♭ g`. In particular, this construction does not rely
on [function extensionality](foundation.function-extensionality.md).

## Definitions

### The flat modality's action on homotopies

```agda
module _
  {@♭ l1 l2 : Level} {@♭ A : UU l1} {@♭ B : A → UU l2} {@♭ f g : (x : A) → B x}
  where

  ap-flat-htpy :
    @♭ f ~ g → ap-dependent-map-flat f ~ ap-dependent-map-flat g
  ap-flat-htpy H (cons-flat x) = eq-cons-flat-crisp-eq (H x)
```

## Properties

### Computing the flat action on the reflexivity homotopy

```agda
module _
  {@♭ l1 l2 : Level} {@♭ A : UU l1} {@♭ B : A → UU l2} {@♭ f : (x : A) → B x}
  where

  compute-ap-flat-refl-htpy : ap-flat-htpy (refl-htpy' f) ~ refl-htpy
  compute-ap-flat-refl-htpy (cons-flat x) = compute-refl-eq-cons-flat-crisp-eq
```
