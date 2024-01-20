# Crisp cartesian product types

```agda
{-# OPTIONS --cohesion --flat-split #-}

module modal-type-theory.crisp-cartesian-product-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.functoriality-cartesian-product-types
open import foundation.functoriality-dependent-pair-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.retractions
open import foundation.sections
open import foundation.universe-levels

open import modal-type-theory.crisp-dependent-pair-types
open import modal-type-theory.flat-discrete-crisp-types
open import modal-type-theory.flat-modality
```

</details>

## Idea

We say a [cartesian product type](foundation-core.cartesian-product-types.md) is
{{#concept "crisp" Disambigiation="cartesian product type"}} if it is formed in
a crisp context.

## Properties

### Flat distributes over cartesian product types

This is Theorem 6.9 of _Brouwer's fixed-point theorem in real-cohesive homotopy
type theory_.

```agda
module _
  {@♭ l1 l2 : Level} {@♭ A : UU l1} {@♭ B : UU l2}
  where

  map-distributive-flat-prod : ♭ (A × B) → (♭ A) × (♭ B)
  pr1 (map-distributive-flat-prod (cons-flat (x , y))) = cons-flat x
  pr2 (map-distributive-flat-prod (cons-flat (x , y))) = cons-flat y

  map-inv-distributive-flat-prod : (♭ A) × (♭ B) → ♭ (A × B)
  map-inv-distributive-flat-prod (cons-flat x , cons-flat y) = cons-flat (x , y)

  is-section-map-distributive-flat-prod :
    is-section map-inv-distributive-flat-prod map-distributive-flat-prod
  is-section-map-distributive-flat-prod (cons-flat x) = refl

  is-retraction-map-distributive-flat-prod :
    is-retraction map-inv-distributive-flat-prod map-distributive-flat-prod
  is-retraction-map-distributive-flat-prod (cons-flat x , cons-flat y) = refl

  section-distributive-flat-prod : section map-distributive-flat-prod
  pr1 section-distributive-flat-prod = map-inv-distributive-flat-prod
  pr2 section-distributive-flat-prod = is-retraction-map-distributive-flat-prod

  retraction-distributive-flat-prod : retraction map-distributive-flat-prod
  pr1 retraction-distributive-flat-prod = map-inv-distributive-flat-prod
  pr2 retraction-distributive-flat-prod = is-section-map-distributive-flat-prod

  is-equiv-map-distributive-flat-prod : is-equiv map-distributive-flat-prod
  pr1 is-equiv-map-distributive-flat-prod = section-distributive-flat-prod
  pr2 is-equiv-map-distributive-flat-prod = retraction-distributive-flat-prod

  distributive-flat-prod : ♭ (A × B) ≃ (♭ A) × (♭ B)
  pr1 distributive-flat-prod = map-distributive-flat-prod
  pr2 distributive-flat-prod = is-equiv-map-distributive-flat-prod

  inv-distributive-flat-prod : (♭ A) × (♭ B) ≃ ♭ (A × B)
  inv-distributive-flat-prod = inv-equiv distributive-flat-prod
```

### Computing the flat counit on a cartesian product type

The counit of the flat modality computes as the counit on each component of a
crisp dependent pair type.

```agda
module _
  {@♭ l1 l2 : Level} {@♭ A : UU l1} {@♭ B : UU l2}
  where

  compute-counit-flat-prod :
    counit-flat {A = A × B} ~
    ( map-prod counit-flat counit-flat ∘ map-distributive-flat-prod)
  compute-counit-flat-prod (cons-flat x) = refl
```

### A crisp cartesian product type is flat discrete if both factors are

```agda
module _
  {@♭ l1 l2 : Level} {@♭ A : UU l1} {@♭ B : UU l2}
  where

  is-flat-discrete-crisp-prod :
    is-flat-discrete-crisp A →
    is-flat-discrete-crisp B →
    is-flat-discrete-crisp (A × B)
  is-flat-discrete-crisp-prod is-disc-A is-disc-B =
    is-equiv-left-map-triangle
      ( counit-flat)
      ( map-prod counit-flat counit-flat)
      ( map-distributive-flat-prod)
      ( λ where (cons-flat _) → refl)
      ( is-equiv-map-distributive-flat-prod)
      ( is-equiv-map-prod counit-flat counit-flat is-disc-A is-disc-B)

  is-flat-discrete-crisp-right-factor-is-flat-discrete-crisp-prod :
    is-flat-discrete-crisp (A × B) →
    (x : A) →
    is-flat-discrete-crisp B
  is-flat-discrete-crisp-right-factor-is-flat-discrete-crisp-prod
    is-disc-prod-A-B x =
    is-equiv-right-factor-is-equiv-map-prod
      ( counit-flat)
      ( counit-flat)
      ( x)
      ( is-equiv-right-map-triangle
        counit-flat
        ( map-prod counit-flat counit-flat)
        ( map-distributive-flat-prod)
        ( λ where (cons-flat _) → refl)
        ( is-disc-prod-A-B)
        ( is-equiv-map-distributive-flat-prod))

  is-flat-discrete-crisp-left-factor-is-flat-discrete-crisp-prod :
    is-flat-discrete-crisp (A × B) →
    (x : B) →
    is-flat-discrete-crisp A
  is-flat-discrete-crisp-left-factor-is-flat-discrete-crisp-prod
    is-disc-prod-A-B x =
    is-equiv-left-factor-is-equiv-map-prod
      ( counit-flat)
      ( counit-flat)
      ( x)
      ( is-equiv-right-map-triangle
        counit-flat
        ( map-prod counit-flat counit-flat)
        ( map-distributive-flat-prod)
        ( λ where (cons-flat _) → refl)
        ( is-disc-prod-A-B)
        ( is-equiv-map-distributive-flat-prod))
```

## References

- Michael Shulman, _Brouwer's fixed-point theorem in real-cohesive homotopy type
  theory_, 2015 ([arXiv:1509.07584](https://arxiv.org/abs/1509.07584))
- Dan Licata, _cohesion-agda_, GitHub repository
  (<https://github.com/dlicata335/cohesion-agda>)
