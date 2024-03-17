# Crisp dependent function types

```agda
{-# OPTIONS --cohesion --flat-split #-}

module modal-type-theory.crisp-dependent-function-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.postcomposition-dependent-functions
open import foundation.postcomposition-functions
open import foundation.retractions
open import foundation.sections
open import foundation.universe-levels

open import modal-type-theory.action-on-identifications-crisp-functions
open import modal-type-theory.action-on-identifications-flat-modality
open import modal-type-theory.crisp-identity-types
open import modal-type-theory.flat-modality
open import modal-type-theory.functoriality-flat-modality
```

</details>

## Idea

We say a dependent function type is
{{#concept "crisp" Disambigiation="dependent function type"}} if it is formed in
a [crisp context](modal-type-theory.crisp-types.md).

## Properties

### Flat distributes in one direction over dependent function types

```agda
module _
  {@♭ l1 l2 : Level} {@♭ A : UU l1} {@♭ B : @♭ A → UU l2}
  where

  map-distributive-flat-crisp-Π : ♭ ((@♭ x : A) → B x) → ((@♭ x : A) → ♭ (B x))
  map-distributive-flat-crisp-Π (intro-flat f) x = intro-flat (f x)

module _
  {@♭ l1 l2 : Level} {@♭ A : UU l1} {@♭ B : A → UU l2}
  where

  map-distributive-flat-Π :
    ♭ ((x : A) → B x) → ((x : ♭ A) → action-flat-family B x)
  map-distributive-flat-Π (intro-flat f) (intro-flat x) = intro-flat (f x)
```

### Postcomposition by the counit induces an equivalence under the flat modality on dependent function types

This is Theorem 6.14 in {{#cite Shu18}}.

```agda
module _
  {@♭ l1 l2 : Level} {@♭ A : UU l1} {@♭ B : @♭ A → UU l2}
  where

  map-action-flat-dependent-map-postcomp-counit-flat :
    ♭ ((u : ♭ A) → action-flat-crisp-family B u) →
    ♭ ((u : ♭ A) → family-over-flat B u)
  map-action-flat-dependent-map-postcomp-counit-flat (intro-flat f) =
    intro-flat (λ where (intro-flat x) → counit-flat (f (intro-flat x)))

  map-inv-action-flat-dependent-map-postcomp-counit-flat :
    ♭ ((u : ♭ A) → family-over-flat B u) →
    ♭ ((u : ♭ A) → action-flat-crisp-family B u)
  map-inv-action-flat-dependent-map-postcomp-counit-flat (intro-flat f) =
    intro-flat (λ where (intro-flat y) → intro-flat (f (intro-flat y)))

  is-section-map-inv-action-flat-dependent-map-postcomp-counit-flat :
    is-section
      ( map-action-flat-dependent-map-postcomp-counit-flat)
      ( map-inv-action-flat-dependent-map-postcomp-counit-flat)
  is-section-map-inv-action-flat-dependent-map-postcomp-counit-flat
    (intro-flat f) =
    ap-flat (eq-htpy (λ where (intro-flat x) → refl))

  is-retraction-map-inv-action-flat-dependent-map-postcomp-counit-flat :
    is-retraction
      ( map-action-flat-dependent-map-postcomp-counit-flat)
      ( map-inv-action-flat-dependent-map-postcomp-counit-flat)
  is-retraction-map-inv-action-flat-dependent-map-postcomp-counit-flat
    (intro-flat f) =
    ap-flat
      ( eq-htpy
        ( λ where
          (intro-flat x) → is-crisp-retraction-intro-flat (f (intro-flat x))))

  is-equiv-action-flat-depdendent-map-postcomp-counit-flat :
    is-equiv map-action-flat-dependent-map-postcomp-counit-flat
  is-equiv-action-flat-depdendent-map-postcomp-counit-flat =
    is-equiv-is-invertible
      ( map-inv-action-flat-dependent-map-postcomp-counit-flat)
      ( is-section-map-inv-action-flat-dependent-map-postcomp-counit-flat)
      ( is-retraction-map-inv-action-flat-dependent-map-postcomp-counit-flat)

  equiv-action-flat-depdendent-map-postcomp-counit-flat :
    ♭ ((u : ♭ A) → action-flat-crisp-family B u) ≃
    ♭ ((u : ♭ A) → family-over-flat B u)
  equiv-action-flat-depdendent-map-postcomp-counit-flat =
    ( map-action-flat-dependent-map-postcomp-counit-flat ,
      is-equiv-action-flat-depdendent-map-postcomp-counit-flat)
```

## See also

- [Flat discrete types](modal-type-theory.flat-discrete-crisp-types.md) for
  types that are flat modal.

## References

{{#bibliography}} {{#reference Shu18}} {{#reference Dlicata335/Cohesion-Agda}}
