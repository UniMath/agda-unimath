# The action on homotopies of the flat modality

```agda
{-# OPTIONS --cohesion --flat-split #-}

module modal-type-theory.action-on-homotopies-flat-modality where
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

open import modal-type-theory.action-on-identifications-crisp-functions
open import modal-type-theory.action-on-identifications-flat-modality
open import modal-type-theory.crisp-identity-types
open import modal-type-theory.flat-modality
open import modal-type-theory.functoriality-flat-modality
```

</details>

## Idea

Given a crisp [homotopy](foundation-core.homotopies.md) of maps `f ~ g`, then
there is a homotopy `♭ f ~ ♭ g` where `♭ f` is the
[functorial action of the flat modality on maps](modal-type-theory.functoriality-flat-modality.md).

## Definitions

### The flat modality's action on crisp homotopies

```agda
module _
  {@♭ l1 l2 : Level} {@♭ A : UU l1} {@♭ B : @♭ A → UU l2}
  {@♭ f g : (@♭ x : A) → B x}
  where

  ap-crisp-htpy-flat :
    @♭ ((@♭ x : A) → f x ＝ g x) →
    ap-crisp-dependent-map-flat f ~ ap-crisp-dependent-map-flat g
  ap-crisp-htpy-flat H (cons-flat x) = ap-flat (H x)
```

### The flat modality's action on homotopies

```agda
module _
  {@♭ l1 l2 : Level} {@♭ A : UU l1} {@♭ B : A → UU l2}
  {@♭ f g : (x : A) → B x}
  where

  ap-htpy-flat : @♭ f ~ g → ap-dependent-map-flat f ~ ap-dependent-map-flat g
  ap-htpy-flat H = ap-crisp-htpy-flat (λ x → H x)
```

## Properties

### Computing the flat action on the reflexivity homotopy

```agda
module _
  {@♭ l1 l2 : Level} {@♭ A : UU l1} {@♭ B : A → UU l2} {@♭ f : (@♭ x : A) → B x}
  where

  compute-ap-crisp-flat-refl-htpy :
    ap-crisp-htpy-flat (λ x → (refl {x = f x})) ~ refl-htpy
  compute-ap-crisp-flat-refl-htpy (cons-flat x) = refl
```
