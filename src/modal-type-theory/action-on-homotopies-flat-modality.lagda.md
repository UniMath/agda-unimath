# The action on homotopies of the flat modality

```agda
{-# OPTIONS --cohesion --flat-split #-}

module modal-type-theory.action-on-homotopies-flat-modality where
```

<details><summary>Imports</summary>

```agda
open import foundation.homotopies
open import foundation.identity-types
open import foundation.universe-levels

open import modal-type-theory.action-on-identifications-flat-modality
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

  action-flat-crisp-htpy :
    @♭ ((@♭ x : A) → f x ＝ g x) →
    action-flat-crisp-dependent-map f ~ action-flat-crisp-dependent-map g
  action-flat-crisp-htpy H (intro-flat x) = ap-flat (H x)
```

### The flat modality's action on homotopies

```agda
module _
  {@♭ l1 l2 : Level} {@♭ A : UU l1} {@♭ B : A → UU l2}
  {@♭ f g : (x : A) → B x}
  where

  action-flat-htpy :
    @♭ f ~ g → action-flat-dependent-map f ~ action-flat-dependent-map g
  action-flat-htpy H = action-flat-crisp-htpy (λ x → H x)
```

## Properties

### Computing the flat action on the reflexivity homotopy

```agda
module _
  {@♭ l1 l2 : Level} {@♭ A : UU l1} {@♭ B : A → UU l2} {@♭ f : (@♭ x : A) → B x}
  where

  compute-action-flat-refl-htpy :
    action-flat-crisp-htpy (λ x → (refl {x = f x})) ~ refl-htpy
  compute-action-flat-refl-htpy (intro-flat x) = refl
```
