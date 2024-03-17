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

open import modal-type-theory.action-on-identifications-crisp-functions
open import modal-type-theory.action-on-identifications-flat-modality
open import modal-type-theory.crisp-dependent-function-types
open import modal-type-theory.crisp-identity-types
open import modal-type-theory.flat-modality
open import modal-type-theory.functoriality-flat-modality
```

</details>

## Idea

We say a [function type](foundation-core.function-types.md) is
{{#concept "crisp" Disambigiation="function type"}} if it is formed in a
[crisp context](modal-type-theory.crisp-types.md).

<!-- TODO explain crisp function vs crisply defined function (nonstandard terminology, find better name) -->

## Properties

### Flat distributes in one direction over dependent function types

```agda
module _
  {@♭ l1 l2 : Level} {@♭ A : UU l1} {@♭ B : UU l2}
  where

  map-distributive-flat-crisp-function-types : ♭ (@♭ A → B) → (@♭ A → ♭ B)
  map-distributive-flat-crisp-function-types = map-distributive-flat-crisp-Π

  map-distributive-flat-function-types : ♭ (A → B) → (♭ A → ♭ B)
  map-distributive-flat-function-types f (intro-flat x) =
    map-distributive-flat-Π f (intro-flat x)
```

### Postcomposition by the counit induces an equivalence `♭ (♭ A → ♭ B) ≃ ♭ (♭ A → B)`

This is Theorem 6.14 in {{#cite Shu18}}.

```agda
module _
  {@♭ l1 l2 : Level} {@♭ A : UU l1} {@♭ B : UU l2}
  where

  map-inv-action-flat-map-postcomp-counit-flat : ♭ (♭ A → B) → ♭ (♭ A → ♭ B)
  map-inv-action-flat-map-postcomp-counit-flat (intro-flat f) =
    intro-flat (λ where (intro-flat y) → intro-flat (f (intro-flat y)))

  is-section-map-inv-action-flat-map-postcomp-counit-flat :
    is-section
      ( action-flat-map (postcomp (♭ A) counit-flat))
      ( map-inv-action-flat-map-postcomp-counit-flat)
  is-section-map-inv-action-flat-map-postcomp-counit-flat (intro-flat f) =
    ap-flat (eq-htpy (λ where (intro-flat _) → refl))

  is-retraction-map-inv-action-flat-map-postcomp-counit-flat :
    is-retraction
      ( action-flat-map (postcomp (♭ A) counit-flat))
      ( map-inv-action-flat-map-postcomp-counit-flat)
  is-retraction-map-inv-action-flat-map-postcomp-counit-flat (intro-flat f) =
    ap-flat
      ( eq-htpy
        ( λ where
          (intro-flat x) → is-crisp-retraction-intro-flat (f (intro-flat x))))

  is-equiv-action-flat-map-postcomp-counit-flat :
    is-equiv (action-flat-map (postcomp (♭ A) (counit-flat {A = B})))
  is-equiv-action-flat-map-postcomp-counit-flat =
    is-equiv-is-invertible
      ( map-inv-action-flat-map-postcomp-counit-flat)
      ( is-section-map-inv-action-flat-map-postcomp-counit-flat)
      ( is-retraction-map-inv-action-flat-map-postcomp-counit-flat)

  equiv-action-flat-map-postcomp-counit-flat : ♭ (♭ A → ♭ B) ≃ ♭ (♭ A → B)
  pr1 equiv-action-flat-map-postcomp-counit-flat =
    action-flat-map (postcomp (♭ A) counit-flat)
  pr2 equiv-action-flat-map-postcomp-counit-flat =
    is-equiv-action-flat-map-postcomp-counit-flat
```

## See also

- [Flat discrete types](modal-type-theory.flat-discrete-crisp-types.md) for
  types that are flat modal.

## References

{{#bibliography}} {{#reference Shu18}} {{#reference Dlicata335/Cohesion-Agda}}
