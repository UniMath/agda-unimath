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

open import modal-type-theory.crisp-identity-types
open import modal-type-theory.flat-modality
```

</details>

## Idea

The [flat modality](modal-type-theory.flat-modality.md) is functorial.

- Given a map `f : A → B`, there is a map `♭f : ♭ A → ♭ B`
- Given two composable maps `f` and `g`, the image of their composite computes
  as `♭(g ∘ f) ~ ♭g ∘ ♭f`
- The identity is mapped to the identity.

## Definition

### The flat modality's action on type families

```agda
module _
  {@♭ l1 l2 : Level} {@♭ A : UU l1}
  where

  flat-crisp-family : @♭ (@♭ A → UU l2) → ♭ A → UU l2
  flat-crisp-family B (cons-flat x) = ♭ (B x)

  flat-family : @♭ (A → UU l2) → ♭ A → UU l2
  flat-family B = flat-crisp-family (crispen B)
```

### The flat modality's action on maps

```agda
module _
  {@♭ l1 l2 : Level} {@♭ A : UU l1}
  where

  ap-crisp-dependent-map-flat :
    {@♭ B : @♭ A → UU l2} →
    @♭ ((@♭ x : A) → B x) → ((x : ♭ A) → flat-crisp-family B x)
  ap-crisp-dependent-map-flat f (cons-flat x) = cons-flat (f x)

  ap-dependent-map-flat :
    {@♭ B : A → UU l2} → @♭ ((x : A) → B x) → ((x : ♭ A) → flat-family B x)
  ap-dependent-map-flat f = ap-crisp-dependent-map-flat (crispen f)

module _
  {@♭ l1 l2 : Level} {@♭ A : UU l1} {@♭ B : UU l2}
  where

  ap-crisp-map-flat : @♭ (@♭ A → B) → (♭ A → ♭ B)
  ap-crisp-map-flat f (cons-flat x) =
    ap-crisp-dependent-map-flat f (cons-flat x)

  ap-map-flat : @♭ (A → B) → (♭ A → ♭ B)
  ap-map-flat f = ap-crisp-map-flat (crispen f)
```

### The flat modality's coaction on maps

```agda
module _
  {@♭ l1 l2 : Level} {@♭ A : UU l1} {@♭ B : UU l2}
  where

  coap-map-flat : (♭ A → ♭ B) → (@♭ A → B)
  coap-map-flat f x = counit-flat (f (cons-flat x))

  is-crisp-retraction-coap-map-flat :
    (@♭ f : @♭ A → B) → coap-map-flat (ap-crisp-map-flat f) ＝ f
  is-crisp-retraction-coap-map-flat _ = refl
```

## Properties

### Naturality of the counit

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
    (@♭ f : A → B) → counit-flat ∘ ap-map-flat f ~ f ∘ counit-flat
  naturality-counit-flat f (cons-flat x) = refl
```

### Functoriality of the action on maps

```agda
module _
  {@♭ l1 : Level} {@♭ A : UU l1}
  where

  preserves-id-ap-map-flat : ap-map-flat (id {A = A}) ~ id
  preserves-id-ap-map-flat (cons-flat x) = refl

module _
  {@♭ l1 l2 l3 : Level} {@♭ A : UU l1} {@♭ B : UU l2} {@♭ C : UU l3}
  where

  preserves-comp-ap-map-flat :
    (@♭ f : A → B) (@♭ g : B → C) →
    ap-map-flat (g ∘ f) ~ ap-map-flat g ∘ ap-map-flat f
  preserves-comp-ap-map-flat f g (cons-flat x) = refl
```

### The functorial action preserves equivalences

```agda
module _
  {@♭ l1 l2 : Level} {@♭ A : UU l1} {@♭ B : UU l2} {@♭ f : A → B}
  where

  ap-section-flat : @♭ section f → section (ap-map-flat f)
  pr1 (ap-section-flat (g , H)) = ap-map-flat g
  pr2 (ap-section-flat (g , H)) (cons-flat x) = crisp-ap cons-flat (H x)

  ap-retraction-flat : @♭ retraction f → retraction (ap-map-flat f)
  pr1 (ap-retraction-flat (g , H)) = ap-map-flat g
  pr2 (ap-retraction-flat (g , H)) (cons-flat x) = crisp-ap cons-flat (H x)

  is-equiv-ap-is-equiv-map-flat : @♭ is-equiv f → is-equiv (ap-map-flat f)
  pr1 (is-equiv-ap-is-equiv-map-flat (s , r)) = ap-section-flat s
  pr2 (is-equiv-ap-is-equiv-map-flat (s , r)) = ap-retraction-flat r

module _
  {@♭ l1 l2 : Level} {@♭ A : UU l1} {@♭ B : UU l2}
  where

  ap-retract-flat : @♭ (A retract-of B) → ♭ A retract-of ♭ B
  pr1 (ap-retract-flat (f , r)) = ap-map-flat f
  pr2 (ap-retract-flat (f , r)) = ap-retraction-flat r

  ap-equiv-flat : @♭ (A ≃ B) → ♭ A ≃ ♭ B
  pr1 (ap-equiv-flat (f , H)) = ap-map-flat f
  pr2 (ap-equiv-flat (f , H)) = is-equiv-ap-is-equiv-map-flat H
```

## See also

- In [the flat-sharp adjunction](modal-type-theory.flat-sharp-adjunction.md) we
  postulate that the flat modality is left adjoint to the
  [sharp modality](modal-type-theory.sharp-modality.md).
- [Flat discrete types](modal-type-theory.flat-discrete-crisp-types.md) for
  types that are flat modal.

## References

- Michael Shulman, _Brouwer's fixed-point theorem in real-cohesive homotopy type
  theory_, 2015 ([arXiv:1509.07584](https://arxiv.org/abs/1509.07584))
- Dan Licata, _cohesion-agda_, GitHub repository
  (<https://github.com/dlicata335/cohesion-agda>)
