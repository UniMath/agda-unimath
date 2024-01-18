# Crisp function types

```agda
{-# OPTIONS --cohesion --flat-split #-}

module modal-type-theory.crisp-function-types where
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
open import foundation.postcomposition-functions
open import foundation.retractions
open import foundation.sections
open import foundation.universe-levels

open import modal-type-theory.crisp-dependent-function-types
open import modal-type-theory.crisp-identity-types
open import modal-type-theory.flat-modality
open import modal-type-theory.functoriality-flat-modality
```

</details>

## Idea

We say a [function type](foundation-core.function-types.md) is
{{#concept "crisp" Disambigiation="function type"}} if it is formed in a crisp
context.

## Properties

### Flat distributes over dependent function types

```agda
module _
  {@♭ l1 l2 : Level} {@♭ A : UU l1} {@♭ B : UU l2}
  where

  map-crisp-distributive-flat-function-types : ♭ (A → B) → (@♭ A → ♭ B)
  map-crisp-distributive-flat-function-types = map-crisp-distributive-flat-Π

  map-distributive-flat-function-types : ♭ (A → B) → (♭ A → ♭ B)
  map-distributive-flat-function-types f (cons-flat x) =
    map-crisp-distributive-flat-function-types f x
```

### Postcomposition by the counit induces an equivalence `♭ (♭ B → ♭ A) ≃ ♭ (♭ B → A)`

This is Theorem 6.14 in _Brouwer's fixed-point theorem in real-cohesive homotopy
type theory_.

```agda
module _
  {@♭ l1 l2 : Level} {@♭ A : UU l1} {@♭ B : UU l2}
  where

  map-inv-ap-map-flat-postcomp-counit-flat : ♭ (♭ B → A) → ♭ (♭ B → ♭ A)
  map-inv-ap-map-flat-postcomp-counit-flat (cons-flat f) =
    cons-flat (λ where (cons-flat y) → cons-flat (f (cons-flat y)))

  is-section-map-inv-ap-map-flat-postcomp-counit-flat :
    is-section
      ( ap-map-flat (postcomp (♭ B) counit-flat))
      ( map-inv-ap-map-flat-postcomp-counit-flat)
  is-section-map-inv-ap-map-flat-postcomp-counit-flat (cons-flat f) =
    crisp-ap cons-flat (eq-htpy (λ where (cons-flat _) → refl))

  is-retraction-map-inv-ap-map-flat-postcomp-counit-flat :
    is-retraction
      ( ap-map-flat (postcomp (♭ B) counit-flat))
      ( map-inv-ap-map-flat-postcomp-counit-flat)
  is-retraction-map-inv-ap-map-flat-postcomp-counit-flat (cons-flat f) =
    crisp-ap cons-flat
      ( eq-htpy
        ( λ where
          (cons-flat x) → is-crisp-retraction-cons-flat (f (cons-flat x))))

  is-equiv-ap-map-flat-postcomp-counit-flat :
    is-equiv (ap-map-flat (postcomp (♭ B) (counit-flat {A = A})))
  is-equiv-ap-map-flat-postcomp-counit-flat =
    is-equiv-is-invertible
      ( map-inv-ap-map-flat-postcomp-counit-flat)
      ( is-section-map-inv-ap-map-flat-postcomp-counit-flat)
      ( is-retraction-map-inv-ap-map-flat-postcomp-counit-flat)

  equiv-ap-map-flat-postcomp-counit-flat : ♭ (♭ B → ♭ A) ≃ ♭ (♭ B → A)
  pr1 equiv-ap-map-flat-postcomp-counit-flat =
    ap-map-flat (postcomp (♭ B) counit-flat)
  pr2 equiv-ap-map-flat-postcomp-counit-flat =
    is-equiv-ap-map-flat-postcomp-counit-flat
```

## See also

- [Flat discrete types](modal-type-theory.flat-discrete-crisp-types.md) for
  types that are flat modal.

## References

- Michael Shulman, _Brouwer's fixed-point theorem in real-cohesive homotopy type
  theory_, 2015 ([arXiv:1509.07584](https://arxiv.org/abs/1509.07584))
- Dan Licata, _cohesion-agda_, GitHub repository
  (<https://github.com/dlicata335/cohesion-agda>)
