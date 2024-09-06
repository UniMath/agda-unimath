# Functoriality of the flat modality

```agda
{-# OPTIONS --cohesion --flat-split #-}

module modal-type-theory.functoriality-flat-modality where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.retractions
open import foundation.retracts-of-types
open import foundation.sections
open import foundation.universe-levels

open import modal-type-theory.action-on-identifications-flat-modality
open import modal-type-theory.flat-modality
```

</details>

## Idea

The [flat modality](modal-type-theory.flat-modality.md) is functorial.

- Given a map `f : A → B`, there is a map `♭f : ♭ A → ♭ B`
- Given two composable maps `f` and `g`, the image of their composite computes
  as `♭(g ∘ f) ~ ♭g ∘ ♭f`
- The identity is mapped to the identity.

## Definitions

### The flat modality's action on type families

```agda
module _
  {@♭ l1 l2 : Level} {@♭ A : UU l1}
  where

  action-flat-crisp-family : @♭ (@♭ A → UU l2) → ♭ A → UU l2
  action-flat-crisp-family B (intro-flat x) = ♭ (B x)

  action-flat-family : @♭ (A → UU l2) → ♭ A → UU l2
  action-flat-family B = action-flat-crisp-family (crispen B)
```

### The flat modality's action on maps

```agda
module _
  {@♭ l1 l2 : Level} {@♭ A : UU l1}
  where

  action-flat-crisp-dependent-map :
    {@♭ B : @♭ A → UU l2} →
    @♭ ((@♭ x : A) → B x) →
    ((x : ♭ A) → action-flat-crisp-family B x)
  action-flat-crisp-dependent-map f (intro-flat x) = intro-flat (f x)

  action-flat-dependent-map :
    {@♭ B : A → UU l2} →
    @♭ ((x : A) → B x) →
    ((x : ♭ A) → action-flat-family B x)
  action-flat-dependent-map f = action-flat-crisp-dependent-map (crispen f)

module _
  {@♭ l1 l2 : Level} {@♭ A : UU l1} {@♭ B : UU l2}
  where

  action-flat-crisp-map : @♭ (@♭ A → B) → (♭ A → ♭ B)
  action-flat-crisp-map f (intro-flat x) =
    action-flat-crisp-dependent-map f (intro-flat x)

  action-flat-map : @♭ (A → B) → (♭ A → ♭ B)
  action-flat-map f = action-flat-crisp-map (crispen f)
```

### The flat modality's coaction on maps

```agda
module _
  {@♭ l1 l2 : Level} {@♭ A : UU l1} {@♭ B : UU l2}
  where

  coap-map-flat : (♭ A → ♭ B) → (@♭ A → B)
  coap-map-flat f x = counit-flat (f (intro-flat x))

  is-crisp-retraction-coap-map-flat :
    (@♭ f : @♭ A → B) → coap-map-flat (action-flat-crisp-map f) ＝ f
  is-crisp-retraction-coap-map-flat _ = refl
```

## Properties

### Naturality of the flat counit

The counit of the flat modality is natural with respect to the action on maps:
we have [commuting squares](foundation-core.commuting-squares-of-maps.md)

```text
               ♭ f
         ♭ A ------> ♭ B
          |           |
 counit-♭ |           | counit-♭
          ∨           ∨
          A --------> B.
                f
```

```agda
module _
  {@♭ l1 l2 : Level} {@♭ A : UU l1} {@♭ B : UU l2}
  where

  naturality-counit-flat :
    (@♭ f : A → B) → counit-flat ∘ action-flat-map f ~ f ∘ counit-flat
  naturality-counit-flat f (intro-flat x) = refl
```

### Functoriality of the action on maps

```agda
module _
  {@♭ l1 : Level} {@♭ A : UU l1}
  where

  preserves-id-action-flat-map : action-flat-map (id {A = A}) ~ id
  preserves-id-action-flat-map (intro-flat x) = refl

module _
  {@♭ l1 l2 l3 : Level} {@♭ A : UU l1} {@♭ B : UU l2} {@♭ C : UU l3}
  where

  preserves-comp-action-flat-map :
    (@♭ f : A → B) (@♭ g : B → C) →
    action-flat-map (g ∘ f) ~ action-flat-map g ∘ action-flat-map f
  preserves-comp-action-flat-map f g (intro-flat x) = refl
```

### The functorial action preserves equivalences

```agda
module _
  {@♭ l1 l2 : Level} {@♭ A : UU l1} {@♭ B : UU l2} {@♭ f : A → B}
  where

  action-flat-section : @♭ section f → section (action-flat-map f)
  pr1 (action-flat-section (g , H)) = action-flat-map g
  pr2 (action-flat-section (g , H)) (intro-flat x) = ap-flat (H x)

  action-flat-retraction : @♭ retraction f → retraction (action-flat-map f)
  pr1 (action-flat-retraction (g , H)) = action-flat-map g
  pr2 (action-flat-retraction (g , H)) (intro-flat x) = ap-flat (H x)

  is-equiv-ap-is-equiv-map-flat : @♭ is-equiv f → is-equiv (action-flat-map f)
  is-equiv-ap-is-equiv-map-flat (s , r) =
    ( action-flat-section s , action-flat-retraction r)

module _
  {@♭ l1 l2 : Level} {@♭ A : UU l1} {@♭ B : UU l2}
  where

  action-flat-retract : @♭ (A retract-of B) → ♭ A retract-of ♭ B
  action-flat-retract (f , r) = (action-flat-map f , action-flat-retraction r)

  action-flat-equiv : @♭ (A ≃ B) → ♭ A ≃ ♭ B
  action-flat-equiv (f , H) =
    (action-flat-map f , is-equiv-ap-is-equiv-map-flat H)
```

## See also

- In [the flat-sharp adjunction](modal-type-theory.flat-sharp-adjunction.md) we
  postulate that the flat modality is left adjoint to the
  [sharp modality](modal-type-theory.sharp-modality.md).
- [Flat discrete crisp types](modal-type-theory.flat-discrete-crisp-types.md)
  for crisp types that are flat modal.

## References

{{#bibliography}} {{#reference Shu18}} {{#reference Dlicata335/Cohesion-Agda}}
